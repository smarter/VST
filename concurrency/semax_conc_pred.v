Require Import msl.msl_standard.
Require Import msl.seplog.
Require Import veric.base.
Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.juicy_mem_ops.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.semax.
Require Import veric.semax_call.
Require Import veric.semax_ext.
Require Import veric.semax_ext_oracle.
Require Import veric.juicy_safety.
Require Import veric.Clight_new.
Require Import veric.res_predicates.
Require Import veric.SeparationLogic.
Require Import sepcomp.semantics.
Require Import sepcomp.extspec.
Require Import floyd.reptype_lemmas.
Require Import floyd.field_at.
Require Import floyd.nested_field_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import concurrency.lksize.

Definition positive_mpred (R : mpred) :=
  forall phi, app_pred R phi -> exists l sh rsh k p, phi @ l = YES sh rsh k p.

Program Definition weak_positive_mpred (P: mpred): mpred :=
  fun w => positive_mpred (approx (S (level w)) P).
Next Obligation.
  intros; hnf; intros.
  unfold positive_mpred in *.
  intros.
  apply H0.
  simpl in H1 |- *.
  destruct H1; split; auto.
  apply age_level in H.
  omega.
Defined.

Lemma positive_mpred_nonexpansive:
  nonexpansive weak_positive_mpred.
Proof.
  intros.
  hnf; intros.
  intros n ?.
  simpl in H |- *.
  assert (forall y, (n >= level y)%nat -> (P y <-> Q y)).
  Focus 1. {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  } Unfocus.
  clear H.
  intros; split; intros.
  + hnf in H2 |- *.
    intros.
    apply H2; clear H2.
    simpl in H3 |- *.
    destruct H3; split; auto.
    apply H0; auto.
    apply necR_level in H1.
    omega.
  + hnf in H2 |- *.
    intros.
    apply H2; clear H2.
    simpl in H3 |- *.
    destruct H3; split; auto.
    apply H0; auto.
    apply necR_level in H1.
    omega.
Qed.

Program Definition weak_precise_mpred (P: mpred): mpred :=
  fun w => precise (approx (S (level w)) P).
Next Obligation.
  intros; hnf; intros.
  hnf in H0 |- *.
  intros.
  apply (H0 w); auto.
  + simpl in H1 |- *; destruct H1; split; auto.
    apply age_level in H; omega.
  + simpl in H2 |- *; destruct H2; split; auto.
    apply age_level in H; omega.
Defined.

Lemma precise_mpred_nonexpansive: nonexpansive weak_precise_mpred.
Proof.
  hnf; intros.
  intros n ?.
  simpl in H |- *.
  assert (forall y, (n >= level y)%nat -> (P y <-> Q y)).
  Focus 1. {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  } Unfocus.
  clear H.
  intros.
  split; intros.
  + hnf in H2 |- *; intros; apply (H2 w); auto.
    - destruct H3; split; auto.
      apply H0; auto.
      apply necR_level in H1; omega.
    - destruct H4; split; auto.
      apply H0; auto.
      apply necR_level in H1; omega.
  + hnf in H2 |- *; intros; apply (H2 w); auto.
    - destruct H3; split; auto.
      apply H0; auto.
      apply necR_level in H1; omega.
    - destruct H4; split; auto.
      apply H0; auto.
      apply necR_level in H1; omega.
Qed.

Definition lock_inv : share -> val -> mpred -> mpred :=
  fun sh v R =>
    (EX b : block, EX ofs : _,
      !!(v = Vptr b ofs) &&
      LKspec LKSIZE
        R
        (Share.unrel Share.Lsh sh)
        (Share.unrel Share.Rsh sh)
        (b, Int.unsigned ofs))%logic.

Definition rec_inv sh v (Q R: mpred): Prop :=
  (R = Q * lock_inv sh v (|> R))%logic.

Definition weak_rec_inv sh v (Q R: mpred): mpred :=
  (! (R <=> Q * lock_inv sh v (|> R)))%pred.

Lemma lockinv_isptr sh v R : lock_inv sh v R = (!! expr.isptr v && lock_inv sh v R)%logic.
Proof.
  assert (D : isptr v \/ ~isptr v) by (destruct v; simpl; auto).
  destruct D.
  - rewrite prop_true_andp; auto.
  - rewrite prop_false_andp; auto.
    apply pred_ext.
    + unfold lock_inv. Intros b ofs. subst; simpl in *; tauto.
    + apply FF_left.
Qed.

Lemma unfash_fash_equiv: forall P Q: mpred,
  (P <=> Q |--
  (subtypes.unfash (subtypes.fash P): mpred) <=> (subtypes.unfash (subtypes.fash Q): mpred))%pred.
Proof.
  intros.
  hnf; intros.
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P y <-> app_pred Q y)).
  Focus 1. {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  } Unfocus.
  hnf; intros.
  split; simpl; hnf; intros.
  + apply necR_level in H2.
    rewrite <- H0 by omega.
    auto.
  + apply necR_level in H2.
    rewrite H0 by omega.
    auto.
Qed.

Lemma iffp_equiv: forall P1 Q1 P2 Q2: mpred,
  ((P1 <=> Q1) && (P2 <=> Q2) |-- (P1 <--> P2) <=> (Q1 <--> Q2))%pred.
Proof.
  intros.
  hnf; intros.
  destruct H.
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P1 y <-> app_pred Q1 y)).
  Focus 1. {
    intros; specialize (H y H1).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H2 y). spec H2; [auto |].
    tauto.
  } Unfocus.
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P2 y <-> app_pred Q2 y)).
  Focus 1. {
    intros; specialize (H0 y H2).
    destruct H0.
    specialize (H0 y). spec H0; [auto |].
    specialize (H3 y). spec H3; [auto |].
    tauto.
  } Unfocus.
  split; intros; hnf; intros.
  + split; [destruct H5 as [? _] | destruct H5 as [_ ?]]; intros ? HH; specialize (H5 _ HH).
    - apply necR_level in H4.
      apply necR_level in HH.
      rewrite <- H1, <- H2 by omega.
      auto.
    - apply necR_level in H4.
      apply necR_level in HH.
      rewrite <- H1, <- H2 by omega.
      auto.
  + split; [destruct H5 as [? _] | destruct H5 as [_ ?]]; intros ? HH; specialize (H5 _ HH).
    - apply necR_level in H4.
      apply necR_level in HH.
      rewrite H1, H2 by omega.
      auto.
    - apply necR_level in H4.
      apply necR_level in HH.
      rewrite H1, H2 by omega.
      auto.
Qed.

Lemma sepcon_equiv: forall P1 Q1 P2 Q2: mpred,
  ((P1 <=> Q1) && (P2 <=> Q2) |-- (P1 * P2) <=> (Q1 * Q2))%pred.
Proof.
  intros.
  hnf; intros.
  destruct H.
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P1 y <-> app_pred Q1 y)).
  Focus 1. {
    intros; specialize (H y H1).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H2 y). spec H2; [auto |].
    tauto.
  } Unfocus.
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P2 y <-> app_pred Q2 y)).
  Focus 1. {
    intros; specialize (H0 y H2).
    destruct H0.
    specialize (H0 y). spec H0; [auto |].
    specialize (H3 y). spec H3; [auto |].
    tauto.
  } Unfocus.
  split; intros; hnf; intros.
  + destruct H5 as [w1 [w2 [? [? ?]]]].
    exists w1, w2; split; [| split]; auto.
    - apply necR_level in H4.
      apply join_level in H5.
      rewrite <- H1 by omega; auto.
    - apply necR_level in H4.
      apply join_level in H5.
      rewrite <- H2 by omega; auto.
  + destruct H5 as [w1 [w2 [? [? ?]]]].
    exists w1, w2; split; [| split]; auto.
    - apply necR_level in H4.
      apply join_level in H5.
      rewrite H1 by omega; auto.
    - apply necR_level in H4.
      apply join_level in H5.
      rewrite H2 by omega; auto.
Qed.

Lemma later_equiv: forall P Q: mpred,
  (P <=> Q |-- |> P <=> |> Q)%pred.
Proof.
  intros.
  hnf; intros.
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P y <-> app_pred Q y)).
  Focus 1. {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  } Unfocus.
  hnf; intros.
  split; hnf; intros; simpl in *; intros.
  + specialize (H3 _ H4).
    apply necR_level in H2.
    apply laterR_level in H4.
    rewrite <- H0 by omega.
    auto.
  + specialize (H3 _ H4).
    apply necR_level in H2.
    apply laterR_level in H4.
    rewrite H0 by omega.
    auto.
Qed.

Lemma nonexpansive_lock_inv : forall sh p, nonexpansive (lock_inv sh p).
Proof.
  intros.
  unfold lock_inv.
  apply exists_nonexpansive.
  intros b.
  apply exists_nonexpansive.
  intros y.
  apply (conj_nonexpansive (fun _ => prop (p = Vptr b y))).
  1: apply const_nonexpansive.

  unfold LKspec.
  apply forall_nonexpansive; intros.
  hnf; intros.
  intros n ?.
  assert (forall y: rmap, (n >= level y)%nat -> (app_pred P y <-> app_pred Q y)).
  Focus 1. {
    clear - H.
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  } Unfocus.
  simpl; split; intros.
  + if_tac; auto.
    if_tac; auto.
    destruct H3 as [p0 ?].
    exists p0.
    rewrite H3; f_equal.
    f_equal.
    extensionality ts; clear ts.
    clear H3 H4 H5 p0.
    apply predicates_hered.pred_ext; hnf; intros ? [? ?]; split; auto.
    - apply necR_level in H2.
      rewrite <- H0 by omega; auto.
    - apply necR_level in H2.
      rewrite H0 by omega; auto.
  + if_tac; auto.
    if_tac; auto.
    destruct H3 as [p0 ?].
    exists p0.
    rewrite H3; f_equal.
    f_equal.
    extensionality ts; clear ts.
    clear H3 H4 H5 p0.
    apply predicates_hered.pred_ext; hnf; intros ? [? ?]; split; auto.
    - apply necR_level in H2.
      rewrite H0 by omega; auto.
    - apply necR_level in H2.
      rewrite <- H0 by omega; auto.
Qed.

Lemma rec_inv1_nonexpansive: forall sh v Q,
  nonexpansive (weak_rec_inv sh v Q).
Proof.
  intros.
  unfold weak_rec_inv.
  intros P1 P2.
  eapply predicates_hered.derives_trans; [| apply unfash_fash_equiv].
  eapply predicates_hered.derives_trans; [| apply iffp_equiv].
  apply predicates_hered.andp_right; auto.
  eapply predicates_hered.derives_trans; [| apply sepcon_equiv].
  apply predicates_hered.andp_right.
  Focus 1. {
    intros n ?.
    split; intros; hnf; intros; auto.
  } Unfocus.
  eapply predicates_hered.derives_trans; [| apply nonexpansive_lock_inv].
  apply later_equiv.
Qed.

Lemma rec_inv2_nonexpansive: forall sh v R,
  nonexpansive (fun Q => weak_rec_inv sh v Q R).
Proof.
  intros.
  unfold weak_rec_inv.
  intros P1 P2.
  eapply predicates_hered.derives_trans; [| apply unfash_fash_equiv].
  eapply predicates_hered.derives_trans; [| apply iffp_equiv].
  apply predicates_hered.andp_right.
  Focus 1. {
    intros n ?.
    split; intros; hnf; intros; auto.
  } Unfocus.
  eapply predicates_hered.derives_trans; [| apply sepcon_equiv].
  apply predicates_hered.andp_right; auto.

  intros n ?.
  split; intros; hnf; intros; auto.
Qed.

Lemma positive_weak_positive: forall R,
  positive_mpred R ->
  TT |-- weak_positive_mpred R.
Proof.
  intros.
  change (predicates_hered.derives TT (weak_positive_mpred R)).
  intros w _.
  hnf in H |- *.
  intros; apply H.
  eapply approx_p; eauto.
Qed.

Lemma precise_weak_precise: forall R,
  precise R ->
  TT |-- weak_precise_mpred R.
Proof.
  intros.
  change (predicates_hered.derives TT (weak_precise_mpred R)).
  intros w _.
  hnf in H |- *.
  intros; apply (H w0); auto.
  + eapply approx_p; eauto.
  + eapply approx_p; eauto.
Qed.

Lemma rec_inv_weak_rec_inv: forall sh v Q R,
  rec_inv sh v Q R ->
  TT |-- weak_rec_inv sh v Q R.
Proof.
  intros.
  change (predicates_hered.derives TT (weak_rec_inv sh v Q R)).
  intros w _.
  hnf in H |- *.
  intros.
  rewrite H at 1 4.
  split; intros; hnf; intros; auto.
Qed.

