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

Definition block_size : N := 512.
Definition message : Set := string.

Inductive action : Set :=
| send : message -> N -> action
| write : message -> action
| print : string -> action
| request_read : action
| terminate : action.

Inductive protocol_state : Set :=
| waiting_for_init_ack
| waiting_for_next_packet (sendertid : N) (blockid : N)
| waiting_for_last_ack (sendertid : N) (lastblockid : N)
| waiting_for_read (sendertid : N) (blockid : N).

Record state : Set := mkState
 { fsm : protocol_state
 ; previousMessage : option message
 ; mytid : N
 ; actions : list action
 }.
Inductive input_event : Set :=
| incoming : message -> N -> input_event
| read : message -> input_event
(* | eof : input_event *)
| timeout : input_event.

(* Monadic code inspired by  http://adam.chlipala.net/poplmark/compile/coqdoc/MemMonad.html *)
Definition serverM (ret : Set) := state -> state * option ret.
(* TODO thinking about including an action writer in the used Monad to have multiple possible actions + error semantics (fail action) *)

Definition Return (T : Set) (v : T) : serverM T :=
  fun m => (m, Some v).

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

(*  operations on state *)
Definition GetFSM : serverM protocol_state :=
  fun m => (m, Some (fsm m)).
Definition SetFSM (s : protocol_state) : serverM unit :=
  fun m => (mkState s (previousMessage m) (mytid m) (actions m), Some tt).
Definition GetPreviousMessage' : serverM (option message) :=
  fun m => (m, Some (previousMessage m)).
Definition GetPreviousMessage : serverM message :=
  fun m => (m, previousMessage m).
Definition DoAction (a : action) : serverM unit :=
  fun m => (mkState (fsm m) (previousMessage m) (mytid m) (a :: actions m), Some tt).
Definition Send' (msg : message) (to : N) : serverM unit :=
  DoAction (send msg to).
Definition Write (data : string) : serverM unit := DoAction (write data).
Definition RequestRead : serverM unit := DoAction (request_read).
Definition PrintLn (data : string) : serverM unit := DoAction (print data).
Definition Terminate : serverM unit := DoAction terminate.

Definition Fail (T : Set) : serverM T := fun m => (m, None).

Definition Fail' (msg : string) : serverM unit := PrintLn msg;; Terminate. (* this is a version for debugging *)
(* Definition Fail' (msg : string) : serverM unit := Fail unit. *)

Definition LiftOption (T : Set) (may : option T) : serverM T := fun m => (m, may).


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
| FileNotFound
| AccessViolation
| DiskFullOrAllocationExceeded
| IllegalTFTPOperation
| UnknownTransferId
| FileAlreadyExists
| NoSuchUser.

Local Open Scope N_scope.
Definition SerializeErrorCode (ec : ErrorCode) : N :=
  match ec with
  | NotDefined => 0
  | FileNotFound => 1
  | AccessViolation => 2
  | DiskFullOrAllocationExceeded => 3
  | IllegalTFTPOperation => 4
  | UnknownTransferId => 5
  | FileAlreadyExists => 6
  | NoSuchUser => 7
  end.

Definition DeserializeErrorCode (x : N) : option ErrorCode :=
  match x with
  | 0 => Some NotDefined
  | 1 => Some FileNotFound
  | 2 => Some AccessViolation
  | 3 => Some DiskFullOrAllocationExceeded
  | 4 => Some IllegalTFTPOperation
  | 5 => Some UnknownTransferId
  | 6 => Some FileAlreadyExists
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
  PrintLn ("Local error: " ++ msg);;
  Send (ERROR ec msg) errdestination;;
  Terminate.

Definition initialize_upload (tid : N) (port : N) (f : string): state := (* TODO *)
  (mkState waiting_for_init_ack (None) tid [send (Serialize (WRQ f)) port]).

Definition initialize_download (tid : N) (port : N) (f : string): state :=
  (mkState waiting_for_init_ack (None) tid [send (Serialize (RRQ f)) port]).

Definition handle_send_next_block (sendertid : N) (ackedblockid : N): serverM unit :=
  SetFSM (waiting_for_read sendertid (ackedblockid + 1));;
  RequestRead.

Definition process_step_upload (event : input_event) : serverM unit :=
  match event with
  | incoming msg sender =>
    tftpmsg <- ParseMessage msg;
    st <- GetFSM;
    match st with
    | waiting_for_init_ack =>
      match tftpmsg with
      | ACK 0 => handle_send_next_block sender 0
      | ERROR _ msg => PrintLn ("remote error: " ++ msg);; Terminate
      | _ => FailWith NotDefined "Unexpected message" sender
      end
    | waiting_for_next_packet sendertid expectedblockid =>
       if N.eqb sender sendertid then (* check if we received the message from the server or somewhere else and if the source is incorrect, send an error and continue *)
         match tftpmsg with
         | ACK incomingblockid =>
           if incomingblockid =? expectedblockid then
             handle_send_next_block sendertid incomingblockid
           else if incomingblockid <? expectedblockid then
             Return tt (* probably earlier ACK has been retransmitted, so we ignore it *)
           else
             FailWith IllegalTFTPOperation "Unexpected block id (too big)" sender (* received a future block id, but this shouldn't happen in interleaved DATA-ACK scheme, so it must be an error *)
         | ERROR _ msg => PrintLn ("remote error: " ++ msg);; Terminate
         | _ => FailWith IllegalTFTPOperation "Unexpected message" sender
         end
       else Send (ERROR UnknownTransferId "Unknown transfer ID") sender
    | waiting_for_read _ _ => Fail' "I was requesting a read, not socket recv"
    | waiting_for_last_ack sendertid lastblockid =>
      match tftpmsg with
      | ACK incomingblockid =>
        if incomingblockid =? lastblockid then
          PrintLn "Upload complete";; Terminate
        else if incomingblockid <? lastblockid then
          Return tt (* probably earlier ACK has been retransmitted, so we ignore it *)
        else
          FailWith IllegalTFTPOperation "Unexpected block id (too big)" sender
      | ERROR _ msg => PrintLn ("remote error: " ++ msg);; Terminate
      | _ => FailWith IllegalTFTPOperation "Unexpected message" sender
      end
    end
  | timeout => Fail' "TODO timeout"
  | read data =>
    st <- GetFSM;
    match st with
    | waiting_for_read sendertid blockid =>
      Send (DATA blockid data) sendertid;;
      if N_of_nat (length data) <? block_size then (* if we did not read a full block it means it was the last block, so we should start the termination process *)
        SetFSM (waiting_for_last_ack sendertid blockid)
      else
        SetFSM (waiting_for_next_packet sendertid blockid)
    | _ => Fail' "I was not requesting a file read but got it"
    end
  end.


Definition handle_incoming_data (sender : N) (blockid : N) (data : string) : serverM unit :=
  Write (data);;
  Send (ACK blockid) sender;;
  (if N.of_nat (String.length data) <? 512 then
     (* this was the last block, finish up *)
    PrintLn "Download finished";;
    Terminate
  else
    SetFSM (waiting_for_next_packet sender (blockid + 1))
  ).


Definition process_step_download (event : input_event) : serverM unit :=
  match event with
  | incoming msg sender =>
    tftpmsg <- ParseMessage msg;
    st <- GetFSM;
    match st with
    | waiting_for_init_ack => match tftpmsg with
        | DATA 1 data => handle_incoming_data sender 1 data
        | ERROR _ msg => PrintLn ("remote error: " ++ msg);; Terminate
        | _ => FailWith NotDefined "Unexpected message" sender
      end
    | waiting_for_next_packet sendertid expectedblockid =>
       if N.eqb sender sendertid then (* check if we received the message from the server or somewhere else and if the source is incorrect, send an error and continue *)
         match tftpmsg with
         | DATA incomingblockid data =>
           if incomingblockid =? expectedblockid then
             handle_incoming_data sender incomingblockid data
           else if incomingblockid <? expectedblockid then
             Return tt (* probably earlier block has been retransmitted, so we ignore it *)
           else
             FailWith IllegalTFTPOperation "Unexpected block id (too big)" sender (* received a future block id, but this shouldn't happen in interleaved DATA-ACK scheme, so it must be an error *)
         | ERROR _ msg => PrintLn ("remote error: " ++ msg);; Terminate
         | _ => FailWith NotDefined "Unexpected message" sender
         end
       else Send (ERROR UnknownTransferId "Unknown transfer ID") sender
    | waiting_for_read _ _ => Fail' "Reading should not be reachable in download"
    | waiting_for_last_ack _ _ =>Fail' "Waiting for last ack should not be reachable in download"
    end
  | timeout => Fail' "TODO timeout"
  | read data => Fail' "Reading in download is not allowed"
  end.
