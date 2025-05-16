Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RV.Helpers.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RD.Helpers.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RC.Helpers.
Require Import PlutusCert.Util.Tactics.

Import PlutusNotations.

Require Import Arith.
From Coq Require Import Lia.

Lemma Rel'_monotone T T' χ k j t t' :
  Rel' T T' χ ->
  j <= k ->
  χ k t t' ->
  χ j t t'.
Proof with try solve [lia].
  intros H_Rel ? H_chi.
  unfold Rel in *.
  apply H_Rel in H_chi; destruct_hypos...
  assert (j <= k) by lia; auto.
Qed.

Lemma RC_monotone : forall k rho T i e e' ck,
    RD ck rho ->
    RC k T rho e e' ->
    i <= k ->
    RC i T rho e e'.
Proof with (try solve [eauto || lia]).
  intros k rho T i e e' ck HRD HRC Hle__i.

  autorewrite with RC.

  intros j Hlt__j e_f Hev__e.

  apply RC_to_RV with (j := j) (e_f := e_f) in HRC as temp...
  destruct temp as [e'_f [j' [Hev__e'_f HRV]]].

  exists e'_f, j'. split; auto.

  split. eapply RV_typable_empty_1...
  split. eapply RV_typable_empty_2...

  eapply RV_condition in HRV as HRV_cond...

  destruct HRV_cond as [HRV_cond | Herr]...

  destruct T; left.
  all: destruct HRV_cond as [Hnerr__e_f [Hnerr__e'_f HRV_cond]].
  all: split...
  all: split...
  - intros.
    apply RD_sem_syn with (ck := ck) in H as temp...
    destruct temp as [T1 [T2 [Hsyn1 Hsyn2]]].
    remember H as HRel. clear HeqHRel.
    apply RD_Rel with (ck := ck) (T1 := T1) (T2 := T2) in HRel...
    unfold Rel in HRel.
    apply HRel with (j := k - j)...
    eapply HRV_cond...
  - destruct HRV_cond as [x [e_body [e'_body [T1' [T1'a [Heq [Heq' Hfe]]]]]]].
    eexists. eexists. eexists. eexists. eexists.
    split... split...
    intros. eapply Hfe...
  - destruct HRV_cond as [v_0 [v'_0 [F [F' [T [T' [Heq [Heq' Hunwr]]]]]]]].
    eexists. eexists. eexists. eexists. eexists. eexists.
    split... split...
    intros. eapply Hunwr...
  - destruct HRV_cond as [e_body [e'_body [Y [ Z [Heq [Heq' Hie]]]]]].
    eexists. eexists. eexists. eexists.
    split... split...
    intros. eapply Hie...
Qed.

Lemma V_monotone  k Δ ρ T i v v' :
    D Δ ρ ->
    V k T ρ v v' ->
    i <= k ->
    V i T ρ v v'.
Proof with try solve [lia || eauto].
  intros H_D H_V H_lt.
  autorewrite with R in *.
  destruct H_V as [Hty [Hval Hcond]].
  split; [assumption|]; clear Hty.
  split; [assumption|]; clear Hval.
  destruct T...
  - intros χ H_χ.
    assert (H_Rel : exists T1 T2, Rel' T1 T2 χ) by eauto using D_sem_Rel.
    destruct H_Rel as [T1 [T2 H_Rel]].
    eapply Rel'_monotone with (k := k) (j := i)...
    apply Hcond...
  - intros.
    apply Hcond...
  - destruct Hcond as [v_0 [v'_0 [F [F' [T [T' [Heq [Heq' Hunwr]]]]]]]].
    eexists. eexists. eexists. eexists. eexists. eexists.
    split... split...
    intros. eapply Hunwr...
  - destruct Hcond as [e_body [e'_body [Heq [Heq' Hie]]]].
    eexists. eexists.
    split... split...
    intros. eapply Hie...
Qed.

Lemma C_monotone : forall k ρ T i e e' Δ,
    RD Δ ρ ->
    C k T ρ e e' ->
    i <= k ->
    C i T ρ e e'.
Proof with try solve [auto | lia].
  intros k rho T i e e' ck HRD HRC Hle__i.

  autorewrite with R.

  intros j Hlt__j e_f Hev__e.

  run_C HRC e'_f j' H_ev__e' H_V...

  exists e'_f, j'. split; auto.
  destruct H_V.
  - (* values *)
    left. eapply V_monotone;
    admit.
  - (* errors *)
    right...
Admitted.

Lemma RV_monotone : forall k rho T i v v' ck,
    RD ck rho ->
    RV k T rho v v' ->
    i <= k ->
    RV i T rho v v'.
Proof.
  intros k rho T i v v' ck HRD HRV Hlt__i.
  destruct HRV as [Hval__v [Hval__v' HRC]].
  split. auto.
  split. auto.
  eapply RC_monotone. eauto. eauto. eauto.
Qed.

Lemma RG_monotone : forall c ck rho i k env env',
    RD ck rho ->
    RG rho k c env env' ->
    i <= k ->
    RG rho i c env env'.
Proof.
  induction c.
  - intros.
    inversion H0.
    subst.
    constructor.
  - intros.
    inversion H0.
    subst.
    eapply RG_cons; eauto.
    eapply RV_monotone; eauto.
Qed.


Lemma G_monotone : forall c Δ ρ i k env env',
    D Δ ρ ->
    G ρ k c env env' ->
    i <= k ->
    G ρ i c env env'.
Proof.
  induction c.
  - intros.
    inversion H0.
    subst.
    constructor.
  - intros.
    inversion H0.
    subst.
    eapply G_cons; eauto.
    eapply V_monotone; eauto.
Qed.
