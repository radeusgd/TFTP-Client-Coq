Require Import ZArith.
Require Import Coq.Strings.String.
Require Import ZArith.BinInt.
Require Import Ascii.
Require Import List.
Require String.

(* Require Import Binding. *)
Set Implicit Arguments.

Import ListNotations.

Local Open Scope char_scope.

Axiom newline : ascii.
Definition hello := ["h"; "i"].

Definition message : Set := string.
Inductive transfer : Set := upload : message -> transfer | download : message -> transfer.
Inductive action : Set := send : message -> N -> action | terminate : action.

Inductive protocol_state : Set
 := waiting_for_init_ack
  | errored
  | waiting_for_next_packet (sendertid : N) (blockid : nat)
  | finished.

Record state : Set := mkState
 { fsm : protocol_state
 ; previousMessage : option message
 ; mytid : N
 ; actions : list action
 }.
Inductive input_event : Set := incoming : message -> N -> input_event | timeout : input_event.

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

Definition Send (msg : message) (to : N) : serverM unit :=
  DoAction (send msg to).

Definition Fail (T : Set) : serverM T := fun m => (m, None). (* TODO send error ?? *)

Definition LiftOption (T : Set) (may : option T) : serverM T := fun m => (m, may).

Definition Bind (T1 T2 : Set) (M1 : serverM T1) (M2 : T1 -> serverM T2) : serverM T2 :=
  fun m =>
    let (m', v1) := M1 m in
    match v1 with
    | Some v => M2 v m'
    | None => (m', None)
    end.

Class Monad (M : Set -> Set) := {
  MReturn {T: Set} (v: T) : M T ;
  MBind {T1 T2 : Set} (M1 : M T1) (M2 : T1 -> M T2) : M T2
 }.

Instance monad_serverM : Monad serverM :=
 { MReturn := Return; MBind := Bind }.

Notation "x <- m1 ; m2" := (MBind m1 (fun x => m2))
  (right associativity, at level 60).
Notation "m1 ;; m2" := (MBind m1 (fun _ => m2))
  (right associativity, at level 60).

Notation "l1 <+> l2" := (append l1 l2) (right associativity, at level 30).
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

Definition opRRQ := 1.
Definition opDATA := 3.
Definition opACK := 4.
Definition opERROR := 5.

Inductive TFTPMessage : Set
  := RRQ (filename : string)
   | WRQ (filename : string)
   | ERROR (code : N) (message : string)
   | DATA (block : N) (data : string)
   | ACK (block : N).

Definition get_2b_int (msg : message) : option nat := match msg with
  | String a (String b _) => Some ( (256 * (nat_of_ascii a) + (nat_of_ascii b)))
  | _ => None
  end.

Definition nat_to_2b (n : nat) : message := String (ascii_of_nat (n / 256)) (String (ascii_of_nat n) EmptyString).

(* TODO *)
Definition Serialize (msg : TFTPMessage) : string :=
  match msg with
    | RRQ filename => EmptyString
    | WRQ filename => EmptyString
    | ERROR code message => EmptyString
    | DATA block data => EmptyString
    | ACK block => EmptyString
                    end.

Definition Deserialize (data : string) : option TFTPMessage :=
  None.

Theorem SerializationCorrectness : forall m : TFTPMessage, Deserialize (Serialize m) = Some m.
  intros.
  unfold Serialize.
  unfold Deserialize.
  admit.
Admitted. (* TODO *)

Definition get_message_id (msg : message) : option nat := get_2b_int msg.

Fixpoint drop (n: nat) (l : string) : string := match (n, l) with
  | (O, l) => l
  | (_, EmptyString) => EmptyString
  | (S k, String _ t) => drop k t
  end.

Definition get_block_id (msg : message) : option nat := get_2b_int (drop 2 msg).



(* Definition make_RRQ (filename: string) : message := *)
(*   concat [[zero; ascii_of_nat opRRQ]; filename; [zero]; ["o"; "c"; "t"; "e"; "t"]; [zero]]. *)

Definition initialize (tid : N) (port : N) (f : string): state :=
  (mkState waiting_for_init_ack (None) tid [send (Serialize (RRQ f)) port]).

(* Definition make_ACK (blockid : nat) : message := *)
(*   concat [nat_to_2b opACK; nat_to_2b blockid]. *)

(* Definition make_ERROR (errid : nat) : message := *)
(*   concat [nat_to_2b opERROR; nat_to_2b errid; [zero]]. *)

(* Definition get_data : message -> string := drop 4. *)

(* Definition data_length (msg : message) : nat := length (get_data msg). *)

(* Definition handle_incoming_data (sender : N) (blockid : nat) (msg : message) : serverM unit := *)
(*   (* TODO write data to file *) *)
(*   SetFSM (waiting_for_next_packet sender (blockid + 1));; *)
(*   (if data_length msg <? 512 then *)
(*     (* this was the last block, finish up *) *)
(*     SetFSM finished *)
(*   else *)
(*     Return tt);; *)
(*   Send (make_ACK blockid) sender. *)

Definition process_step (event : input_event) : serverM unit :=
  match event with
  | incoming msg sender =>
    tftpmsg <- LiftOption (Deserialize msg);
    st <- GetFSM;
    match st with
    | waiting_for_init_ack => match tftpmsg with
      | DATA 1 data => Fail unit
          (* | Some 1 => handle_incoming_data sender 1 msg *)
      | _ => Fail unit
      end
    | errored => Fail unit (* TODO ? *)
    | waiting_for_next_packet sendertid expectedblockid =>
       if N.eqb sender sendertid then (* check if we received the message from the server or somwehere else and if the source is incorrect, send an error and continue *)
         match tftpmsg with
           | _ => Fail unit
         (* | Some 3 => match get_block_id msg with *)
         (*    | Some incomingblockid => *)
         (*        if incomingblockid =? expectedblockid then *)
         (*          handle_incoming_data sender incomingblockid msg *)
         (*        else if incomingblockid <? expectedblockid then *)
         (*          Return tt (* probably earlier block has been retransmitted, so we ignore it *) *)
         (*        else Fail unit *)
         (*    | _ => Fail unit *)
         (*    end *)
         (* | _ => Fail unit *)
         end
       else Send (Serialize (ERROR 5 "Unknown transfer ID")) sender
    | finished => Fail unit (* TODO *)
    end
  | timeout => Fail unit (* TODO *)
  end.
