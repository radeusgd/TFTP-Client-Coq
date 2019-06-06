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

Theorem ErrorCodeSerializationCorrectness : forall e:ErrorCode, DeserializeErrorCode (SerializeErrorCode e) = Some e.
  intros.
  induction e; simpl; trivial.
Qed.
Local Open Scope N_scope.
Theorem ErrorCodeIsSmall : forall e:ErrorCode, SerializeErrorCode e < 256*256.
  intros.
  induction e; simpl; zify; omega.
Qed.

Lemma ParseNullTerminatedStringCorrectness : forall pref : string, forall rest : string, ParseNullTerminatedString (pref ++ String zero rest) = Some (pref, rest).
  admit.

Admitted.

Lemma ParseNullTerminatedStringCorrectness2 : forall pref : string, ParseNullTerminatedString (pref ++ null) = Some (pref, EmptyString).
  admit.

Admitted.

(* We cannot prove serialization at once, because as for DATA and ACK it works only for messages that contain integers <= 65535 and the general datatype doesn't provide that, instead we'll prove specific instances *)
(* Theorem SerializationCorrectness : forall m : TFTPMessage, Deserialize (Serialize m) = Some m. *)
(*   intros. *)
(*   induction m; unfold Serialize; unfold Deserialize. *)
(*   * simpl. unfold OptBind. *)
(*     rewrite -> ParseNullTerminatedStringCorrectness. *)
(*     simpl. *)
(*     trivial. *)
(*   * simpl. unfold OptBind. *)
(*     rewrite -> ParseNullTerminatedStringCorrectness. *)
(*     simpl. *)
(*     trivial. *)
(*   * unfold OptBind. *)
(*     assert (null = String zero EmptyString). *)
(*   - auto. *)
(*   - rewrite -> H. *)
(*     simpl. *)
(*     rewrite -> ParseNullTerminatedStringCorrectness. *)
(*     simpl. *)
(*     repeat f_equal. *)
(*     repeat rewrite -> N_ascii_embedding. *)
(*     zify. admit. *)

    
  
(*   admit. *)
(* Admitted. (* TODO *) *)

(* Inductive TFTPMessage : Set *)
(*   := RRQ (filename : string) *)
(*    | WRQ (filename : string) *)
(*    | ERROR (code : ErrorCode) (message : string) *)
(*    | DATA (block : N) (data : string) *)
(*    | ACK (block : N). *)
Theorem SerializationCorrectness1 : forall f : string, Deserialize (Serialize (RRQ f)) = Some (RRQ f).
  intros.
  unfold Serialize; unfold Deserialize.
  simpl.
  unfold OptBind.
  rewrite -> ParseNullTerminatedStringCorrectness.
  simpl.
  trivial.
Qed.

Theorem SerializationCorrectness2 : forall f : string, Deserialize (Serialize (WRQ f)) = Some (WRQ f).
  intros.
  unfold Serialize; unfold Deserialize.
  simpl.
  unfold OptBind.
  rewrite -> ParseNullTerminatedStringCorrectness.
  simpl.
  trivial.
Qed.

Definition f (x : N) : N := match x
           with
           | 0 => 0
           | N.pos q => N.pos q~0~0~0~0~0~0~0~0
                            end.

Compute f 4.

Lemma N_rev_mul : forall x:N,
    (match x with
     | 0 => 0
     | N.pos q => N.pos q~0~0~0~0~0~0~0~0
     end) = 256 * x.
  intros.
  simpl.
  trivial.
Qed.

Lemma N_2b_correctness4 : forall x: N,
    (match x / 256 with
     | 0 => 0
     | N.pos q => N.pos q~0~0~0~0~0~0~0~0
     end + x mod 256) = x.
  intros.
  rewrite -> N_rev_mul.
  rewrite -> N.mod_eq.
  remember (256 * (x / 256)) as a.
  assert (a <= x).
  * subst a.
    apply N.mul_div_le.
    zify; omega.
  * zify; omega.
  * zify; omega.
Qed.

Lemma PNTS_rev : forall s:string, (parseNullTerminatedHelper s []) = ParseNullTerminatedString s.
  unfold ParseNullTerminatedString.
  trivial.
Qed.

Lemma div_lemma1 : forall q:N, q < 256 * 256 -> q / 256 < 256.
  intros.
    assert (q <= 256 * 256 - 1).
    ** zify; omega.
    ** assert (q / 256 <= 255).
       *** assert ((256 * 256 - 1) / 256 <= 255).
  - simpl. unfold N.div. simpl. zify. omega.
  - assert (q / 256 <= (256 * 256 - 1) / 256).
    -- apply N.div_le_mono.
       zify; omega. trivial.
    -- rewrite <- H2. zify; omega.
       *** zify; omega.
Qed.
Theorem SerializationCorrectness3 : forall c:ErrorCode, forall m:string, Deserialize (Serialize (ERROR c m)) = Some (ERROR c m).
  intros.
  unfold Serialize; unfold Deserialize.
  unfold OptBind.
  cbn.
  repeat rewrite -> N_ascii_embedding.
  rewrite -> N_2b_correctness4.
  rewrite -> ErrorCodeSerializationCorrectness.
  rewrite -> PNTS_rev.
  rewrite -> ParseNullTerminatedStringCorrectness2.
  simpl.
  trivial.

  apply N.mod_upper_bound.
  zify;omega.

  assert (SerializeErrorCode c < 256 * 256).
  * apply ErrorCodeIsSmall.
  * remember (SerializeErrorCode c) as q.
    destruct Heqq.
    apply div_lemma1. assumption.
Qed.
