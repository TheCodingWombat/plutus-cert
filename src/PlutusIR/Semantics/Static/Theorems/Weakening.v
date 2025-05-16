Require Import PlutusCert.PlutusIR.

Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.
Require Import PlutusCert.Util.List.
Require Import Lists.List.
Import ListNotations.

Module Kinding.

  Lemma weakening : forall Delta Delta' T K,
      inclusion Delta Delta' ->
      Delta |-* T : K ->
      Delta' |-* T : K.
  Proof.
    intros Delta Delta' T K H HT.
    generalize dependent Delta'.
    induction HT.
    all: intros Delta' Hincl.
    all: try solve [econstructor; eauto using inclusion_cons].
  Qed.

  Lemma weakening_empty : forall Delta T K,
      [] |-* T : K ->
      Delta |-* T : K.
  Proof.
    intros.
    eapply weakening; eauto using inclusion_empty.
  Qed.


  Lemma drop_Δ__kinding : forall Δ bs T K,
      drop_Δ Δ bs |-* T : K -> Δ |-* T : K.
  Proof.
    intros.
    eapply Kinding.weakening.
    - apply drop_Δ__inclusion.
    - eauto.
  Qed.

End Kinding.

Module Typing.

  Definition P_has_type Delta Gamma t T : Prop :=
    forall Delta' Gamma',
      inclusion Delta Delta' ->
      inclusion Gamma Gamma' ->
      Delta' ,, Gamma' |-+ t : T.

  Definition P_constructor_well_formed Delta c T : Prop :=
    forall Delta',
      inclusion Delta Delta' ->
      Delta' |-ok_c c : T.

  Definition P_bindings_well_formed_nonrec Delta Gamma bs : Prop :=
    forall Delta' Gamma',
      inclusion Delta Delta' ->
      inclusion Gamma Gamma' ->
      Delta' ,, Gamma' |-oks_nr bs.

  Definition P_bindings_well_formed_rec Delta Gamma bs : Prop :=
    forall Delta' Gamma',
      inclusion Delta Delta' ->
      inclusion Gamma Gamma' ->
      Delta' ,, Gamma' |-oks_r bs.

  Definition P_binding_well_formed Delta Gamma rec b : Prop :=
    forall Delta' Gamma',
      inclusion Delta Delta' ->
      inclusion Gamma Gamma' ->
      Delta' ,, Gamma' |-ok_b rec # b.

  #[export] Hint Unfold
    P_has_type
    P_constructor_well_formed
    P_bindings_well_formed_nonrec
    P_bindings_well_formed_rec
    P_binding_well_formed
    : core.

  Lemma weakening :
    (forall Delta Gamma t T, Delta ,, Gamma |-+ t : T -> P_has_type Delta Gamma t T) /\
    (forall Delta Gamma bs, Delta ,, Gamma |-oks_nr bs -> P_bindings_well_formed_nonrec Delta Gamma bs) /\
    (forall Delta Gamma bs, Delta ,, Gamma |-oks_r bs -> P_bindings_well_formed_rec Delta Gamma bs) /\
    (forall  Delta Gamma rec b, Delta ,, Gamma |-ok_b rec # b -> P_binding_well_formed Delta Gamma rec b).
  Proof with eauto using Kinding.weakening, inclusion_cons, inclusion_append.
    apply has_type__multind with
      (P := P_has_type)
      (P0 := P_constructor_well_formed)
      (P1 := P_bindings_well_formed_nonrec)
      (P2 := P_bindings_well_formed_rec)
      (P3 := P_binding_well_formed).
    all: intros; autounfold.
    all: try (intros Delta'_0 Gamma'_0 HinclD HinclG).
    all: try (intros Delta'_0 HinclD).
    all: try solve [econstructor; subst; eauto using Kinding.weakening, inclusion_cons, inclusion_append].
    - (* TyAbs *)
      unfold P_has_type in H0.
      apply T_TyAbs; auto.
      apply H0.
      apply inclusion_cons; auto.
      eapply drop_ty_var__inclusion_preserving; eauto.
      eapply drop_ty_var__inclusion_preserving; eauto.
    - (* T_Let NonRec*)
      econstructor; subst; eauto using Kinding.weakening, inclusion_cons, inclusion_append.
      apply Kinding.weakening with (Delta := drop_Δ Δ bs); auto.
      apply drop_Δ__preserves__inclusion. assumption.
    - (* T_Let Rec *)
      econstructor; subst; eauto using Kinding.weakening, inclusion_cons, inclusion_append.
      apply Kinding.weakening with (Delta := drop_Δ Δ bs); auto.
      apply drop_Δ__preserves__inclusion. assumption.
    - (* W_Data *)
      econstructor...
      + subst; intros.
        eapply H8...
        apply inclusion_append.
        destruct rec; auto.
        eapply drop_Δ'__preserves__inclusion. assumption.
      + destruct rec; subst...
        simpl in *.
        eapply Kinding.weakening...
        apply inclusion_cons.
        apply inclusion_append.
        eapply drop_Δ'__preserves__inclusion. assumption.
  Qed.

  Lemma weakening_empty : forall Delta Gamma t T,
      [] ,, [] |-+ t : T ->
      Delta ,, Gamma |-+ t : T.
  Proof.
    intros Delta Gamma t T Ht.
    apply weakening in Ht.
    unfold P_has_type in Ht.
    apply Ht.
    - apply inclusion_empty.
    - apply inclusion_empty.
  Qed.

  Corollary weakening_term Delta Delta' Gamma Gamma' t T
    (incl_Delta : inclusion Delta Delta')
    (incl_Gamma : inclusion Gamma Gamma') :
      Delta ,, Gamma |-+ t : T ->
      Delta' ,, Gamma' |-+ t : T.
  Proof.
    intros.
    eapply weakening.
    all: eassumption.
  Qed.

End Typing.
