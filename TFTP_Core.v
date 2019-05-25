Require Import ZArith.
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

Inductive maybe (t : Set) := just : t -> maybe t | nothing : maybe t. 

Definition message : Set := list ascii.
Inductive transfer : Set := upload : message -> transfer | download : message -> transfer.
Inductive action : Set := send : message -> N -> action | continue : action | terminate : action.

Inductive protocol_state : Set
 := waiting_for_init_ack
  | errored
  | waiting_for_next_packet (sendertid : N) (blockid : nat)
  | finished.

Record state : Set := mkState
 { fsm : protocol_state
 ; previousMessage : maybe message
 ; mytid : N
 }.
Inductive input_event : Set := incoming : message -> N -> input_event | timeout : input_event.

(* Monadic code inspired by  file:///home/radeusgd/Projekty/TFTP/reference/MemMonad.html  TODO true link*)
Definition stateM (ret : Set) := state -> state * ret.

Definition SReturn (T : Set) (v : T) : stateM T :=
  fun m => (m, v).

(*  operations on state *)
Definition GetFSM : stateM protocol_state :=
  fun m => (m, fsm m).

Definition SetFSM (s : protocol_state) : stateM unit :=
  fun m => (mkState s (previousMessage m) (mytid m), tt).

Definition SBind (T1 T2 : Set) (M1 : stateM T1) (M2 : T1 -> stateM T2) : stateM T2 :=
  fun m =>
    let (m', v1) := M1 m in
      M2 v1 m'.

Class Monad (M : Set -> Set) := {
  Return {T: Set} (v: T) : M T ;
  Bind {T1 T2 : Set} (M1 : M T1) (M2 : T1 -> M T2) : M T2
 }.

Instance monad_stateM : Monad stateM :=
 { Return := SReturn; Bind := SBind }.

Notation "x <- m1 ; m2" := (Bind m1 (fun x => m2))
  (right associativity, at level 60).
Notation "m1 ;; m2" := (Bind m1 (fun _ => m2))
  (right associativity, at level 60).

Definition append (x : list ascii) (y : list ascii) : list ascii := concat [x; y].

Notation "l1 <+> l2" := (append l1 l2) (right associativity, at level 30).
(*
Definition readMessageM (ret : Set) := message -> message * ret.

Instance monad_readMessageM : Monad readMessageM :=
  { Return T v := fun m => (m,v);
    Bind T1 T2 M1 M2 := fun m =>
    let (m', v1) := M1 m in
      M2 v1 m' }.
*)
Section mspec.
   Variables (T : Set) (P : state -> T -> Prop).

   Definition mspec (m1 : stateM T) (m : state) : Prop :=
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
  
   Variable m1 : stateM T.
   Variable m : state.

  Theorem mspec_imp : mspec P1 m1 m
    -> (forall m v, P1 m v -> P2 m v)
    -> mspec P2 m1 m.
    unfold mspec.
    intuition.
  Qed.
End mspec_imp.

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

   Variable m1 : stateM T1.
   Variable m2 : T1 -> stateM T2.

  Theorem mspec_Bind : forall m,
    mspec (fun m v => mspec P (m2 v) m) m1 m
    -> mspec P (Bind m1 m2) m.
    unfold mspec, Bind, SBind; simpl; intro.
    destruct (m1 m); simpl.
    destruct (m2 t m). unfold SBind. intro. unfold stateM in m1, m2. auto. 
    destruct (m1 m). destruct (m2 t1 s1). destruct (m2 t s) in H. intuition.

  Qed.
End mspec_Bind.
*)

Definition opRRQ := 1.
Definition opDATA := 3.
Definition opACK := 4.
Definition opERROR := 5.

Definition get_2b_int (msg : message) : maybe nat := match msg with
  | a :: b :: _ => just ( (256 * (nat_of_ascii a) + (nat_of_ascii b)))
  | _ => nothing nat
  end.

Definition nat_to_2b (n : nat) : message := [(ascii_of_nat (n / 256)); (ascii_of_nat n)].

Definition get_message_id (msg : message) : maybe nat := get_2b_int msg.

Fixpoint drop {T : Set} (n: nat) (l : list T) : list T := match (n, l) with
  | (O, l) => l
  | (_, []) => []
  | (S k, _ :: t) => drop k t
  end.

Definition get_block_id (msg : message) : maybe nat := get_2b_int (drop 2 msg).

Definition make_RRQ (filename: list ascii) : message :=
  concat [[zero; ascii_of_nat opRRQ]; filename; [zero]; ["o"; "c"; "t"; "e"; "t"]; [zero]].

Definition initialize (tid : N) (port : N) (f : list ascii): state * action :=
  (mkState waiting_for_init_ack (nothing message) tid, send (make_RRQ f) port).

Definition fail : stateM action := Return terminate. (* TODO send error *)

Definition make_ACK (blockid : nat) : message :=
  concat [nat_to_2b opACK; nat_to_2b blockid].

Definition make_ERROR (errid : nat) : message :=
  concat [nat_to_2b opERROR; nat_to_2b errid; [zero]].

Definition get_data : message -> list ascii := drop 4.

Definition data_length (msg : message) : nat := length (get_data msg).

Definition handle_incoming_data (sender : N) (blockid : nat) (msg : message) : stateM action :=
  SetFSM (waiting_for_next_packet sender (blockid + 1));;
  (if data_length msg <? 512 then
    (* this was the last block, finish up *)
    SetFSM finished
  else
    Return tt);;
  Return (send (make_ACK blockid) sender).

Definition process_step (event : input_event) : stateM action :=
  match event with
  | incoming msg sender => 
    st <- GetFSM;
    match st with
    | waiting_for_init_ack => match get_message_id msg with
      | just 3 => match get_block_id msg with
          | just 1 => handle_incoming_data sender 1 msg
          | _ => fail
          end
      | _ => fail
      end
    | errored => Return (terminate)
    | waiting_for_next_packet sendertid expectedblockid => 
       if N.eqb sender sendertid then
         match get_message_id msg with
         | just 3 => match get_block_id msg with
            | just incomingblockid =>
                if incomingblockid =? expectedblockid then
                  handle_incoming_data sender incomingblockid msg
                else if incomingblockid <? expectedblockid then
                  Return continue (* probably earlier block has been retransmitted, so we ignore it *)
                else fail
            | _ => fail
            end
         | _ => fail
         end
       else Return (send (make_ERROR 5) sender)
    | finished => Return (terminate)
    end
  | timeout => Return (terminate)
  end.
