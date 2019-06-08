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

Theorem SerializationCorrectness4 : forall b:N, forall m:string, b < 256*256 -> Deserialize (Serialize (DATA b m)) = Some (DATA b m).
  intros.
  unfold Serialize; unfold Deserialize.
  unfold OptBind.
  cbn.
  repeat rewrite -> N_ascii_embedding.
  rewrite -> N_2b_correctness4.
  trivial.

  apply N.mod_upper_bound.
  zify;omega.

  apply div_lemma1. assumption.
Qed.

Theorem SerializationCorrectness5 : forall b:N, b < 256*256 -> Deserialize (Serialize (ACK b)) = Some (ACK b).
  intros.
  unfold Serialize; unfold Deserialize.
  unfold OptBind.
  cbn.
  repeat rewrite -> N_ascii_embedding.
  rewrite -> N_2b_correctness4.
  trivial.

  apply N.mod_upper_bound.
  zify;omega.

  apply div_lemma1. assumption.
Qed.


Definition Run (m : serverM unit) (st : state) : option state :=
  option_map fst (m st).

Definition Fails (m : serverM unit) (st : state) : Prop :=
  Run m st = None.

Definition Satisfies (m : serverM unit) (st : state) (prop : state -> Prop) : Prop :=
  match Run m st with
  | Some st1 => prop st1
  | None => False
  end.

Definition DoesNotFail (m : serverM unit) (st : state) : Prop :=
  Satisfies m st (fun s => True).

Definition Sends (msg : TFTPMessage) (to : N) (st : state) : Prop :=
  In (send (Serialize msg) to) (actions st).

Definition Writes (data : message) (st : state) : Prop :=
  In (write data) (actions st).

Definition RequestsRead (st : state) : Prop :=
  In (request_read) (actions st).

Definition Terminates (st : state) : Prop :=
  In (terminate) (actions st).

Theorem UploadStartsWithWRQ : forall (tid : N) (port : N) (f : string), Sends (WRQ f) port (initialize_upload tid port f).
  intros.
  unfold initialize_upload.
  unfold Sends.
  simpl.
  auto.
Qed.

Theorem DownloadStartsWithRRQ : forall (tid : N) (port : N) (f : string), Sends (RRQ f) port (initialize_download tid port f).
  intros.
  unfold initialize_upload.
  unfold Sends.
  simpl.
  auto.
Qed.

Ltac mbind := simpl; unfold Bind; simpl.

Ltac urun := unfold Run; unfold option_map.
Ltac ufail := unfold Fail'; unfold Fail.
Ltac ufails := unfold Fails; unfold Run; unfold option_map; trivial.

(* Definition DoesNotReach (prop : state -> Prop) (m : serverM unit) (st : state) : Prop := Fails m st \/ Satisfies m st (fun s => ~ prop s). *)

(* Lemma AnyMessage : forall (m : message) (s : state), ParseMessage m s = None \/ exists (msg : TFTPMessage), ParseMessage m s = Some (s, msg). *)
(*   intros. *)
(*   unfold ParseMessage; unfold LiftOption. unfold Deserialize. *)
(*   destruct m. *)
(*   * simpl. auto. *)
(*   * destruct m. *)
(*   - simpl. auto. *)
(*   - simpl.  *)

(* Theorem DownloadNeverReadsFile : forall (e : input_event) (st : state), DoesNotReach (RequestsRead) (process_step_download e) st. *)
(*   intros. *)
(*   unfold process_step_download. *)
(*   destruct e. *)
(*   * unfold DoesNotReach. *)
(*     ** mbind. *)
       
(*     destruct st. destruct fsm. cbn. *)
(*   * ufail. unfold DoesNotReach. left. ufails. *)
(*   * ufail. unfold DoesNotReach. left. ufails. *)

Lemma LiftOptSome (T : Set) : forall (x:T) (st : state), LiftOption (Some x) st = Some (st, x).
  intros.
  simpl. trivial.
Qed.

Opaque Serialize.
Ltac usat := unfold Satisfies; urun; unfold process_step_download; mbind.
Ltac parse sc := unfold ParseMessage; rewrite sc; rewrite -> LiftOptSome.

Definition DownloadState (st : state) : Prop :=
  fsm st = waiting_for_init_ack \/ exists (s : N) (b : N), fsm st = waiting_for_next_packet s b.

Theorem DownloadTerminatesOnError1 : forall (sender : N) (st : state) (ec : ErrorCode) (em : message), fsm st = waiting_for_init_ack -> Satisfies (process_step_download (incoming (Serialize (ERROR ec em)) sender)) st Terminates.
  intros.
  usat.
  parse SerializationCorrectness3.
  rewrite H.
  simpl.
  unfold Terminates.
  simpl. auto.
Qed.

Theorem DownloadTerminatesOnError2 : forall (sender : N) (b : N) (st : state) (ec : ErrorCode) (em : message), fsm st = waiting_for_next_packet sender b -> Satisfies (process_step_download (incoming (Serialize (ERROR ec em)) sender)) st Terminates.
  intros.
  usat.
  parse SerializationCorrectness3.
  rewrite H.
  simpl.
  unfold Terminates.
  assert (sender =? sender = true).
  * rewrite N.eqb_eq. trivial.
  * rewrite -> H0.
  simpl. auto.
Qed.


Theorem DownloadACKInit : forall (sender : N) (st : state) (data : message), fsm st = waiting_for_init_ack -> Satisfies (process_step_download (incoming (Serialize (DATA 1 data)) sender)) st (fun s => Sends (ACK 1) sender s /\ (N.of_nat (String.length data) < 512 \/ fsm s = waiting_for_next_packet sender 2)).
  intros.
  usat.
  unfold ParseMessage.
  rewrite SerializationCorrectness4.
  rewrite LiftOptSome.
  rewrite H.
  unfold handle_incoming_data.
  simpl. mbind.
  unfold SetFSM. simpl.
  remember (N.of_nat (String.length data) <? 512) as last'.
  destruct last'.
  * simpl.
    unfold Sends. simpl.
    constructor.
    ** auto.
    ** left. apply N.ltb_lt. auto.
  * unfold Sends. simpl.
    constructor.
    ** auto.
    ** right. trivial.
  * zify; omega.
Qed.
