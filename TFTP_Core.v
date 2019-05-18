Require Import ZArith.
Require Import ZArith.BinInt.
Require Import Ascii.
Require Import List.
Require String.

Import ListNotations.

Local Open Scope char_scope.

Axiom newline : ascii.
Definition hello := ["h"; "i"].

Inductive transfer : Set := upload : list ascii -> transfer | download : list ascii -> transfer.
Inductive action : Set := send : list ascii -> Z -> action | terminate : action.
Inductive state : Set := todo : state.
Inductive input_event : Set := incoming : list ascii -> Z -> input_event | timeout : input_event.

Definition incr1 (x : Z): Z :=
  (x + 1).

Theorem incr1_lemma : forall x: Z, Z.lt x (incr1 x).
intros.
unfold incr1.
omega.
Qed.

Definition tst (x: ascii): ascii := x.

Definition tst2 (x: list ascii): list ascii := x.

Definition make_upload (name: list ascii): transfer := upload name.

Definition initialize (tid : Z) (port : Z) (t : transfer) : (action * state) :=
  (send hello port, todo).

Definition process_step (event : input_event) (st : state) : (action * state) :=
  match event with
  | incoming msg sender => (send msg sender, st)
  | timeout => (terminate, st)
  end.
