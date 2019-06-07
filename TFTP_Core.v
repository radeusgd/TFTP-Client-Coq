Require Import ZArith.
Require Import Coq.Strings.String.
Require Import ZArith.BinInt.
Require Import Coq.Strings.Ascii.
Require Import List.
Require Import String.
Require Import Coq.Numbers.Natural.Abstract.NDiv.

(* Require Import Binding. *)
Set Implicit Arguments.

Import ListNotations.


Definition message : Set := string.
Inductive transfer : Set :=
| upload : message -> transfer
| download : message -> transfer.

Inductive action : Set :=
| send : message -> N -> action
| write : message -> action
| request_read : action
| terminate : action.

Inductive protocol_state : Set :=
| waiting_for_init_ack
| errored
| waiting_for_next_packet (sendertid : N) (blockid : N)
| finished.

Record state : Set := mkState
 { fsm : protocol_state
 ; previousMessage : option message
 ; mytid : N
 ; actions : list action
 }.
Inductive input_event : Set :=
| incoming : message -> N -> input_event
| read : message -> input_event
| eof : input_event
| timeout : input_event.

(* Monadic code inspired by  http://adam.chlipala.net/poplmark/compile/coqdoc/MemMonad.html *)
Definition serverM (ret : Set) := state -> state * option ret.
(* TODO thinking about including an action writer in the used Monad to have multiple possible actions + error semantics (fail action) *)

Definition Return (T : Set) (v : T) : serverM T :=
  fun m => (m, Some v).

(*  operations on state *)
Definition GetFSM : serverM protocol_state :=
  fun m => (m, Some (fsm m)).

Definition SetFSM (s : protocol_state) : serverM unit :=
  fun m => (mkState s (previousMessage m) (mytid m) (actions m), Some tt).

Definition DoAction (a : action) : serverM unit :=
  fun m => (mkState (fsm m) (previousMessage m) (mytid m) (a :: actions m), Some tt).

Definition Send' (msg : message) (to : N) : serverM unit :=
  DoAction (send msg to).

Definition Write (data : string) : serverM unit := DoAction (write data).

Definition Fail (T : Set) : serverM T := fun m => (m, None).
Definition Terminate : serverM unit := DoAction terminate.

Definition LiftOption (T : Set) (may : option T) : serverM T := fun m => (m, may).

Definition Bind (T1 T2 : Set) (M1 : serverM T1) (M2 : T1 -> serverM T2) : serverM T2 :=
  fun m =>
    let (m', v1) := M1 m in
    match v1 with
    | Some v => M2 v m'
    | None => (m', None)
    end.

Class Monad (M : Set -> Set) := {
  MBind {T1 T2 : Set} (M1 : M T1) (M2 : T1 -> M T2) : M T2
 }.

Instance monad_serverM : Monad serverM :=
 { MBind := Bind }.

Definition OptBind (T1 T2 : Set) (M1 : option T1) (M2 : T1 -> option T2) : option T2 :=
  match M1 with
  | Some v => M2 v
  | None => None
  end.

Instance monad_option : Monad option :=
  { MBind := OptBind }.

Notation "x <- m1 ; m2" := (MBind m1 (fun x => m2))
  (right associativity, at level 60).
Notation "m1 ;; m2" := (MBind m1 (fun _ => m2))
  (right associativity, at level 60).

(* Notation "l1 <+> l2" := (append l1 l2) (right associativity, at level 30). *)
(*
Definition readMessageM (ret : Set) := message -> message * ret.

Instance monad_readMessageM : Monad readMessageM :=
  { Return T v := fun m => (m,v);
    Bind T1 T2 M1 M2 := fun m =>
    let (m', v1) := M1 m in
      M2 v1 m' }.
 *)

(*
Section mspec.
   Variables (T : Set) (P : state -> T -> Prop).

   Definition mspec (m1 : serverM T) (m : state) : Prop :=
    P (fst (m1 m)) (snd (m1 m)).

   Lemma mspec_Return : forall m v,
    P m v
    -> mspec (Return v) m.
    trivial.
  Qed.
End mspec.

Section mspec_imp.
   Variable T : Set.
   Variables P1 P2 : state -> T -> Prop.
  
   Variable m1 : serverM T.
   Variable m : state.

  Theorem mspec_imp : mspec P1 m1 m
    -> (forall m v, P1 m v -> P2 m v)
    -> mspec P2 m1 m.
    unfold mspec.
    intuition.
  Qed.
End mspec_imp.
*)
(*Section mspec_Read.
   Variable P : memory -> nat -> Prop.
  
   Variable addr : nat.
   Variable m : memory.

  Theorem mspec_Read :
    P m (m addr)
    -> mspec P (Read addr) m.
    trivial.
  Qed.
End mspec_Read.
*)
(*
Section mspec_Bind.
   Variables (T1 T2 : Set) (P : state -> T2 -> Prop).

   Variable m1 : serverM T1.
   Variable m2 : T1 -> serverM T2.

  Theorem mspec_Bind : forall m,
    mspec (fun m v => mspec P (m2 v) m) m1 m
    -> mspec P (Bind m1 m2) m.
    unfold mspec, Bind, SBind; simpl; intro.
    destruct (m1 m); simpl.
    destruct (m2 t m). unfold SBind. intro. unfold serverM in m1, m2. auto. 
    destruct (m1 m). destruct (m2 t1 s1). destruct (m2 t s) in H. intuition.

  Qed.
End mspec_Bind.
*)

Inductive ErrorCode : Set :=
| NotDefined
| UnknownTransferId
| NoSuchUser.

Local Open Scope N_scope.
Definition SerializeErrorCode (ec : ErrorCode) : N :=
  match ec with
  | NotDefined => 0
  | UnknownTransferId => 5
  | NoSuchUser => 7
  end.

Definition DeserializeErrorCode (x : N) : option ErrorCode :=
  match x with
  | 0 => Some NotDefined
  | 5 => Some UnknownTransferId
  | 7 => Some NoSuchUser
  | _ => None
  end.

Inductive TFTPMessage : Set
  := RRQ (filename : string)
   | WRQ (filename : string)
   | ERROR (code : ErrorCode) (message : string)
   | DATA (block : N) (data : string)
   | ACK (block : N).

Local Open Scope N_scope.
Local Open Scope char_scope.
Definition Get_2b_N (msg : message) : option N :=
  match msg with
  | String a (String b _) => Some ( (256%N * (N_of_ascii a) + (N_of_ascii b)))
  | _ => None
  end.

Definition N_to_2b (n : N) : message :=
  String (ascii_of_N (n / 256)) (String (ascii_of_N (n mod 256)) EmptyString).

Definition null : string := String zero EmptyString.

Fixpoint drop (n: nat) (l : string) : string := match (n, l) with
  | (O, l) => l
  | (_, EmptyString) => EmptyString
  | (S k, String _ t) => drop k t
  end.

Definition Serialize (msg : TFTPMessage) : string :=
  match msg with
    | RRQ filename => (N_to_2b 1) ++ filename ++ null ++ "octet" ++ null
    | WRQ filename => (N_to_2b 2) ++ filename ++ null ++ "octet" ++ null
    | DATA block data => (N_to_2b 3) ++ (N_to_2b block) ++ data
    | ACK block => (N_to_2b 4) ++ (N_to_2b block)
    | ERROR code message => (N_to_2b 5) ++ (N_to_2b (SerializeErrorCode code)) ++ message ++ null
  end.

Fixpoint StrFromList (l : list ascii) : string :=
  match l with
  | h :: t => String h (StrFromList t)
  | [] => EmptyString
  end.

Require Import Bool.
Definition eq_ascii (a1 a2 : ascii) :=
  match a1, a2 with
  | Ascii b1 b2 b3 b4 b5 b6 b7 b8, Ascii c1 c2 c3 c4 c5 c6 c7 c8 =>
    (eqb b1 c1) && (eqb b2 c2) && (eqb b3 c3) && (eqb b4 c4) &&
    (eqb b5 c5) && (eqb b6 c6) && (eqb b7 c7) && (eqb b8 c8)
  end.

Fixpoint parseNullTerminatedHelper (data : string) (acc : list ascii) : option (string * string) :=
  match data with
  | String a rest =>
    if eq_ascii a zero then
      Some (StrFromList (rev acc), rest) (*TODO*)
    else
      parseNullTerminatedHelper rest (a :: acc)
  | EmptyString => None
  end.
(* parses first part of data until a null character and returns it as the first argument and the rest of data as the second one *)
Definition ParseNullTerminatedString (data : string) : option (string * string) :=
  parseNullTerminatedHelper data [].

Definition Deserialize (data : string) : option TFTPMessage :=
  msgid <- Get_2b_N data;
  let rest := drop 2 data in
  match msgid with
  | 1 =>
    fxr <- ParseNullTerminatedString rest;
    Some (RRQ (fst fxr))
  | 2 =>
    fxr <- ParseNullTerminatedString rest;
      Some (WRQ (fst fxr))
  | 3 =>
    blockid <- Get_2b_N rest;
      Some (DATA blockid (drop 2 rest))
  | 4 =>
    blockid <- Get_2b_N rest;
      Some (ACK blockid)
  | 5 =>
    code <- Get_2b_N rest;
      mxr <- ParseNullTerminatedString (drop 2 rest);
      ec <- DeserializeErrorCode code;
      Some (ERROR ec (fst mxr))
  | _ => None
  end.


Definition ParseMessage (msg : message) : serverM TFTPMessage := LiftOption (Deserialize msg).
Definition Send (msg : TFTPMessage) (to : N) : serverM unit :=
  Send' (Serialize msg) to.

Definition FailWith (ec : ErrorCode) (msg : string) (errdestination : N) : serverM unit :=
  Send (ERROR ec msg) errdestination;;
  Terminate.

Definition initialize (tid : N) (port : N) (f : string): state :=
  (mkState waiting_for_init_ack (None) tid [send (Serialize (RRQ f)) port]).

Definition handle_incoming_data (sender : N) (blockid : N) (data : string) : serverM unit :=
  Write (data);;
  SetFSM (waiting_for_next_packet sender (blockid + 1));;
  (if N.of_nat (String.length data) <? 512 then
    (* this was the last block, finish up *)
    SetFSM finished
  else
    Return tt);;
  Send (ACK blockid) sender.

Definition process_step (event : input_event) : serverM unit :=
  match event with
  | incoming msg sender =>
    tftpmsg <- ParseMessage msg;
    st <- GetFSM;
    match st with
    | waiting_for_init_ack => match tftpmsg with
      | DATA 1 data => handle_incoming_data sender 1 data
      | _ => FailWith NotDefined "Unexpected message" sender
      end
    | errored => Fail unit (* TODO ? *)
    | waiting_for_next_packet sendertid expectedblockid =>
       if N.eqb sender sendertid then (* check if we received the message from the server or somewhere else and if the source is incorrect, send an error and continue *)
         match tftpmsg with
         | DATA incomingblockid data =>
           if incomingblockid =? expectedblockid then
             handle_incoming_data sender incomingblockid data
           else if incomingblockid <? expectedblockid then
             Return tt (* probably earlier block has been retransmitted, so we ignore it *)
           else
             FailWith NotDefined "Unexpected block id (too big)" sender (* received a future block id, but this shouldn't happen in interleaved DATA-ACK scheme, so it must be an error *)
         | _ => FailWith NotDefined "Unexpected message" sender
         end
       else Send (ERROR UnknownTransferId "Unknown transfer ID") sender
    | finished => Terminate
    end
  | timeout => Fail unit (* TODO *)
  | _ => Fail unit
  end.
