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
  * rewrite -> N_ascii_embedding.
    rewrite -> N_ascii_embedding.
    ** assert (x mod 256 = x - 256 * (x / 256)).
       *** apply N.mod_eq. zify; omega.
       ***
           remember (256 * (x / 256)) as M.
           assert (M <= x).
           **** rewrite -> HeqM. apply N.mul_div_le. zify; omega.
           **** zify; omega.
    ** apply N.mod_upper_bound. zify. omega.
    ** apply N.div_lt_upper_bound.
       *** zify; omega.
       *** trivial.
Qed.

Theorem N_2b_correctness2 : forall x:N, forall a:ascii, forall b:ascii, forall s:string, Get_2b_N (String a (String b EmptyString)) = Some x -> Get_2b_N (String a (String b s)) = Some x.
  intros.
  unfold Get_2b_N.
  unfold Get_2b_N in H.
  trivial.
Qed.
Local Open Scope string_scope.
Local Close Scope N_scope.

Theorem Strings2b : forall s:string, String.length s >= 2 -> (exists a:ascii, exists b:ascii, exists t:string, s = String a (String b t)).
  intros.
  induction s.
  * exfalso.
    unfold String.length in H.
    omega.
  * induction s.
    ** exfalso.
       unfold String.length in H.
       omega.
    ** exists a. exists a0. exists s.
       trivial.
Qed.
Theorem N_2b_correctness3 : forall x:N, forall p:string, forall s:string, String.length p >= 2 -> Get_2b_N p = Some x -> Get_2b_N (p ++ s) = Some x.
  intros.
  induction p.
  * exfalso. unfold String.length in H. omega.
  * induction p.
    ** exfalso. unfold String.length in H. omega.
    **
      apply N_2b_correctness2.
      apply H0.
Qed.
Lemma ParseNullTerminatedStringCorrectness : forall pref : string, forall rest : string, ParseNullTerminatedString (pref ++ String zero rest) = Some (pref, rest).
  admit.

Admitted.

Theorem SerializationCorrectness : forall m : TFTPMessage, Deserialize (Serialize m) = Some m.
  intros.
  induction m; unfold Serialize; unfold Deserialize.
  * simpl. unfold OptBind.
    rewrite -> ParseNullTerminatedStringCorrectness.
    simpl.
    trivial.
  * simpl. unfold OptBind.
    rewrite -> ParseNullTerminatedStringCorrectness.
    simpl.
    trivial.
  * unfold OptBind.
    assert (null = String zero EmptyString).
  - auto.
  - rewrite -> H.
    simpl.
    rewrite -> ParseNullTerminatedStringCorrectness.
    simpl.
    repeat f_equal.
    repeat rewrite -> N_ascii_embedding.
    zify. admit.

    
  
  admit.
Admitted. (* TODO *)
