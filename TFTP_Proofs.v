Require Import ZArith.
Require Import Coq.Strings.String.
Require Import ZArith.BinInt.
Require Import Ascii.
Require Import List.
Require String.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Require Import Coq.Arith.PeanoNat.

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

Definition TFTPMessageIsValid (m : TFTPMessage) : Prop :=
  match m with
  | RRQ _ => True
  | WRQ _ => True
  | ERROR _ _ => True
  | DATA block _ => block < 256 * 256
  | ACK block => block < 256 * 256
  end.

Theorem SerializationCorrectness : forall m : TFTPMessage, TFTPMessageIsValid m -> Deserialize (Serialize m) = Some m.
  intros.
  destruct m.
  * apply SerializationCorrectness1.
  * apply SerializationCorrectness2.
  * apply SerializationCorrectness3.
  * apply SerializationCorrectness4.
    unfold TFTPMessageIsValid in H. trivial.
  * apply SerializationCorrectness5.
    unfold TFTPMessageIsValid in H. trivial.
Qed.

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

Lemma SomeExists (A : Set) (prop : A -> Prop) : forall x:A, prop x -> exists e:A, Some x = Some e /\ prop e.
  intros.
  exists x.
  auto.
Qed.

Theorem UploadStartsWithWRQ :
  forall (tid : N) (port : N) (f : string),
  exists st : state, initialize_upload tid port f = Some st /\ Sends (WRQ f) port st.
  intros.
  unfold initialize_upload.
  unfold Sends.
  unfold Run. unfold option_map. simpl.
  apply SomeExists.
  simpl.
  auto.
Qed.

Theorem DownloadStartsWithRRQ :
  forall (tid : N) (port : N) (f : string),
  exists st : state, initialize_download tid port f = Some st /\ Sends (RRQ f) port st.
  intros.
  unfold initialize_download.
  unfold Sends.
  unfold Run. unfold option_map. simpl.
  apply SomeExists.
  simpl.
  auto.
Qed.

Ltac mbind := simpl; unfold Bind; simpl.

Ltac urun := unfold Run; unfold option_map.
Ltac ufail := unfold Fail'; unfold Fail.
Ltac ufails := unfold Fails; unfold Run; unfold option_map; trivial.

Lemma LiftOptSome (T : Set) : forall (x:T) (st : state), LiftOption (Some x) st = Some (st, x).
  intros.
  simpl. trivial.
Qed.

Opaque Serialize.
Ltac usat := unfold Satisfies; urun; unfold process_step_download; mbind.
Ltac parse := unfold ParseMessage; rewrite SerializationCorrectness.
Ltac tftpmessagevalid := unfold TFTPMessageIsValid; try zify; try omega; auto.

Lemma IfEq (A : Set) : forall (x:N) (t:A) (f:A), (if (x =? x) then t else f) = t.
  intros.
  assert (x =? x = true).
  * rewrite N.eqb_eq. trivial.
  * rewrite H. trivial.
Qed.

Theorem SendSetsPreviousMessage :
  forall (m:TFTPMessage) (t:N) (st:state),
    TFTPMessageIsValid m ->
    Satisfies (Send m t) st (fun st => (previousMessage st = Some (Serialize m, t))).
  intros.
  usat.
  trivial.
Qed.

Theorem DownloadTerminatesOnError1 : forall (sender : N) (st : state) (ec : ErrorCode) (em : message), fsm st = waiting_for_init_ack -> Satisfies (process_step_download (incoming (Serialize (ERROR ec em)) sender)) st Terminates.
  intros.
  usat.
  parse.
  rewrite LiftOptSome.
  rewrite H.
  simpl.
  unfold Terminates.
  simpl. auto.
  * tftpmessagevalid.
Qed.

Theorem DownloadTerminatesOnError2 : forall (sender : N) (b : N) (st : state) (ec : ErrorCode) (em : message), fsm st = waiting_for_next_packet sender b -> Satisfies (process_step_download (incoming (Serialize (ERROR ec em)) sender)) st Terminates.
  intros.
  usat.
  parse.
  rewrite LiftOptSome.
  rewrite H.
  simpl.
  unfold Terminates.
  rewrite IfEq.
  simpl. auto.

  tftpmessagevalid.
Qed.

Theorem DownloadACKInit :
  forall (sender : N) (st : state) (data : message),
    fsm st = waiting_for_init_ack ->
    Satisfies
      (process_step_download (incoming (Serialize (DATA 1 data)) sender))
      st
      (fun s => Sends (ACK 1) sender s /\ (N.of_nat (String.length data) < 512 \/ fsm s = waiting_for_next_packet sender 2)).
  intros.
  usat.
  parse.
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
  * trivial.
    tftpmessagevalid.
Qed.

Theorem DownloadACKNext :
  forall (sender : N) (b : N) (st : state) (data : message),
    fsm st = waiting_for_next_packet sender b ->
    b > 1 ->
    b < 256 * 256 ->
    Satisfies
      (process_step_download (incoming (Serialize (DATA b data)) sender))
      st
      (fun s => Sends (ACK b) sender s /\ ((N.of_nat (String.length data) < 512) \/ fsm s = waiting_for_next_packet sender (b + 1))).
  intros.
  usat.
  parse.
  rewrite LiftOptSome.
  rewrite H.
  repeat rewrite IfEq.
  unfold handle_incoming_data.
  mbind.
  unfold SetFSM. simpl.
  remember (N.of_nat (String.length data) <? 512) as last'.
  destruct last'.
  * simpl.
    unfold Sends. simpl.
    constructor.
    ** auto.
    ** left. apply N.ltb_lt. auto.
  * unfold Sends. simpl.
    auto.
  * trivial.
Qed.

Theorem DonwloadTerminatesOnFinish1 :
  forall (sender : N) (st : state) (data : message),
    fsm st = waiting_for_init_ack ->
    (N.of_nat (String.length data) < 512) ->
    Satisfies
      (process_step_download (incoming (Serialize (DATA 1 data)) sender))
      st
      Terminates.
  intros.
  usat.
  parse.
  rewrite LiftOptSome.
  rewrite H.
  unfold handle_incoming_data.
  mbind.
  assert (N.of_nat (String.length data) <? 512 = true).
  * rewrite N.ltb_lt. trivial.
  * rewrite H1.
    unfold Terminate. unfold Terminates. simpl. auto.
  * tftpmessagevalid.
Qed.

Theorem DonwloadTerminatesOnFinish2 :
  forall (sender : N) (b : N) (st : state) (data : message),
    fsm st = waiting_for_next_packet sender b ->
    b < 256 * 256 ->
    (N.of_nat (String.length data) < 512) ->
    Satisfies
      (process_step_download (incoming (Serialize (DATA b data)) sender))
      st
      Terminates.
  intros.
  usat.
  parse.
  rewrite LiftOptSome.
  rewrite H.
  unfold handle_incoming_data.
  mbind.
  repeat rewrite IfEq.
  assert (N.of_nat (String.length data) <? 512 = true).
  * rewrite N.ltb_lt. trivial.
  * rewrite H2.
    unfold Terminate. unfold Terminates. simpl. auto.
  * trivial.
Qed.

Theorem DownloadWritesAllData1 :
  forall (sender : N) (st : state) (data : message),
    fsm st = waiting_for_init_ack ->
    Satisfies
      (process_step_download (incoming (Serialize (DATA 1 data)) sender))
      st
      (Writes data).
  intros.
  usat.
  parse.
  rewrite LiftOptSome.
  rewrite H.
  unfold handle_incoming_data.
  mbind.
  remember (N.of_nat (String.length data) <? 512) as last'.
  destruct last'; simpl; unfold Writes; simpl; auto.
  * tftpmessagevalid.
Qed.

Theorem DownloadWritesAllData2 :
  forall (sender : N) (b : N) (st : state) (data : message),
    fsm st = waiting_for_next_packet sender b ->
    b < 256 * 256 ->
    Satisfies
      (process_step_download (incoming (Serialize (DATA b data)) sender))
      st
      (Writes data).
  intros.
  usat.
  parse.
  rewrite LiftOptSome.
  rewrite H.
  repeat rewrite IfEq.
  unfold handle_incoming_data.
  mbind.
  remember (N.of_nat (String.length data) <? 512) as last'.
  destruct last'; simpl; unfold Writes; simpl; auto.

  trivial.
Qed.

Theorem DownloadResendOnTimeout3Times :
  forall (sender : N) (st : state) (m : TFTPMessage),
    TFTPMessageIsValid m ->
    previousMessage st = Some (Serialize m, sender) ->
    retries st < 3 ->
    Satisfies
      (process_step_download (timeout))
      st
      (Sends m sender).
  intros.
  usat.
  unfold retry_after_timeout.
  mbind.
  assert (retries st <? 3 = true).
  * apply N.ltb_lt. trivial.
  * rewrite H2.
    unfold GetPreviousMessage.
    mbind.
    rewrite H0.
    rewrite LiftOptSome.
    unfold Send'. unfold DoAction. simpl.
    unfold Sends. simpl. auto.
Qed.

Theorem DownloadFailAfter3rdTimeout :
  forall (st : state),
    retries st >= 3 ->
    Satisfies
      (process_step_download timeout)
      st
      Terminates.
  intros.
  usat.
  unfold retry_after_timeout.
  mbind.
  assert (~(retries st <? 3 = true)).
  * rewrite N.ltb_lt.
    zify; omega.
  * assert (retries st <? 3 = false).
    destruct (retries st <? 3).
    ** exfalso. auto.
    ** trivial.
    ** rewrite H1.
       unfold Terminates. simpl. auto.
Qed.

Theorem DownloadTimeoutDoesNotChangeFSM :
  forall(s1:state),
    Satisfies (process_step_download timeout) s1 (fun s2 => fsm s2 = fsm s1) \/ Fails (process_step_download timeout) s1.
  intros.
  usat.
  unfold retry_after_timeout.
  mbind.
  remember (retries s1 <? 3) as rets.
  destruct rets.
  remember (previousMessage s1) as pm.
  * destruct pm.
    ** simpl. auto.
    ** simpl.
       right.
       unfold Fails. unfold Run. unfold option_map.
       rewrite <- Heqrets.
       cbn.
       unfold GetPreviousMessage.
       rewrite <- Heqpm.
       unfold LiftOption.
       trivial.
  * left.
    cbn.
    trivial.
Qed.

Fixpoint ExtractRead (al : list action) : (list action * bool) :=
  match al with
  | a :: t =>
    match a with
    | request_read => (t, true)
    | _ => let (t', b) := ExtractRead t in (a :: t', b)
    end
  | [] => ([], false)
  end.

Fixpoint HandleReads (data : list message) (m : serverM unit) : serverM unit :=
  fun st => match m st with
         | Some m' =>
           let (st', _) := m' in
           let (al', wantsread) := ExtractRead (actions st') in
           let st'' := HelperSetActions al' st' in
           if wantsread then
             match data with
             | d :: t => HandleReads t (process_step_upload (read d)) st''
             | [] => process_step_upload (read EmptyString) st''
             end
           else
             Some (st'', tt)
         | None => None
         end.

Theorem UploadReplyToInit :
  forall (sender : N) (st : state) (data : message),
    actions st = [] ->
    fsm st = waiting_for_init_ack ->
    Satisfies
      (HandleReads [data] (process_step_upload (incoming (Serialize (ACK 0)) sender)))
      st
      (fun s => Sends (DATA 1 data) sender s /\ ((N.of_nat (String.length data) < 512 /\ fsm s = waiting_for_last_ack sender 1) \/ fsm s = waiting_for_next_packet sender 1)).
  intros.
  usat.
  parse.
  rewrite LiftOptSome.
  rewrite H0.
  simpl.
  remember (N.of_nat (String.length data) <? block_size) as last'.
  destruct last'.
  * simpl.
    rewrite H. simpl.
    unfold Sends. unfold HelperSetActions; simpl.
    constructor.
    ** auto.
    ** left.
       constructor.
       apply N.ltb_lt.
       auto.
       trivial.
  * simpl.
    rewrite H. simpl.
    unfold Sends. unfold HelperSetActions; simpl.
    constructor.
    ** auto.
    ** auto.
  * simpl. zify. omega.
Qed.

Theorem UploadSendData :
  forall (sender : N) (b : N) (st : state) (data : message),
    fsm st = waiting_for_next_packet sender b ->
    actions st = [] ->
    b > 1 ->
    b < 256 * 256 ->
    Satisfies
      (HandleReads [data] (process_step_upload (incoming (Serialize (ACK b)) sender)))
      st
      (fun s => Sends (DATA (b + 1) data) sender s /\ ((N.of_nat (String.length data) < 512 /\ fsm s = waiting_for_last_ack sender (b + 1)) \/ fsm s = waiting_for_next_packet sender (b + 1))).
  intros.
  usat.
  parse.
  rewrite LiftOptSome.
  rewrite H.
  repeat rewrite IfEq.
  unfold handle_incoming_data.
  mbind.
  unfold SetFSM. simpl.
  remember (N.of_nat (String.length data) <? block_size) as last'.
  destruct last'.
  * simpl.
    unfold Sends.
    rewrite H0.
    simpl.
    constructor.
    ** auto.
    ** left.
       constructor.
       apply N.ltb_lt.
       auto.
       auto.
  * simpl.
    unfold Sends.
    rewrite H0.
    simpl.
    constructor.
    ** auto.
    ** right.
       trivial.
  * trivial.
Qed.

Theorem UploadResendOnTimeout3Times :
  forall (sender : N) (st : state) (m : TFTPMessage),
    TFTPMessageIsValid m ->
    previousMessage st = Some (Serialize m, sender) ->
    retries st < 3 ->
    Satisfies
      (process_step_upload (timeout))
      st
      (Sends m sender).
  intros.
  usat.
  unfold retry_after_timeout.
  mbind.
  assert (retries st <? 3 = true).
  * apply N.ltb_lt. trivial.
  * rewrite H2.
    unfold GetPreviousMessage.
    mbind.
    rewrite H0.
    rewrite LiftOptSome.
    unfold Send'. unfold DoAction. simpl.
    unfold Sends. simpl. auto.
Qed.

Theorem UploadFailAfter3rdTimeout :
  forall (st : state),
    retries st >= 3 ->
    Satisfies
      (process_step_upload timeout)
      st
      Terminates.
  intros.
  usat.
  unfold retry_after_timeout.
  mbind.
  assert (~(retries st <? 3 = true)).
  * rewrite N.ltb_lt.
    zify; omega.
  * assert (retries st <? 3 = false).
    destruct (retries st <? 3).
    ** exfalso. auto.
    ** trivial.
    ** rewrite H1.
       unfold Terminates. simpl. auto.
Qed.

(* Theorem DonwloadTerminatesOnFinish1 : *)
(*   forall (sender : N) (st : state) (data : message), *)
(*     fsm st = waiting_for_init_ack -> *)
(*     (N.of_nat (String.length data) < 512) -> *)
(*     Satisfies *)
(*       (process_step_download (incoming (Serialize (DATA 1 data)) sender)) *)
(*       st *)
(*       Terminates. *)
