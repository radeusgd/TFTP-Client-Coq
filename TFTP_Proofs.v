Require Import ZArith.
Require Import Coq.Strings.String.
Require Import ZArith.BinInt.
Require Import Ascii.
Require Import List.
Require String.
Require Import Coq.Numbers.Natural.Abstract.NDiv.

(* Require Import Binding. *)
Set Implicit Arguments.

Import ListNotations.

Local Open Scope char_scope.
Local Open Scope N_scope.

Require Import TFTP_Core.

Theorem N_2b_correctness1 : forall x:N, (x < 256*256) -> Get_2b_N (N_to_2b x) = Some x.
  intros.
  unfold N_to_2b, Get_2b_N.
  f_equal.
  assert (N_of_ascii
            (ascii_of_N (x / 256)) = x / 256).
  * apply N_ascii_embedding.
    assert (256 * (x/256) <= x).
    ** eapply N.mul_div_le. zify; omega.
    ** zify; omega.
  * assert (N_of_ascii (ascii_of_N (x mod 256)) = x mod 256).
    ** apply N_ascii_embedding. apply N.mod_upper_bound. zify; omega.
    ** assert (x mod 256 = x - 256 * (x / 256)).
       *** apply N.mod_eq. zify; omega.
       *** rewrite -> H0. rewrite -> H1.
           rewrite -> H2.
           remember (256 * (x / 256)) as M.
           assert (M <= x).
           **** rewrite -> HeqM. apply N.mul_div_le. zify; omega.
           **** zify; omega.
Qed.

Theorem SerializationCorrectness : forall m : TFTPMessage, Deserialize (Serialize m) = Some m.
  intros.
  unfold Serialize.
  unfold Deserialize.
  admit.
Admitted. (* TODO *)
