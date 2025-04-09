Require Import PlutusCert.PlutusIR.
From PlutusCert Require Import BoundVars.

Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.
Require Import PlutusCert.Util.List.
Require Import Lists.List.
Import ListNotations.

Module Kinding.

  Lemma weakening : forall Δ Δ' T K,
      inclusion Δ Δ' ->
      kctx_wf Δ ->
      kctx_wf Δ' ->
      Forall (fun X => lookup X Δ' = None) (Ty.btv T) ->
      Δ |-* T : K ->
      Δ' |-* T : K.
  Proof.
    intros Δ Δ' T K H HT.
    generalize dependent Δ'.
    induction HT.
    all: intros Δ' Hincl.
    all: try solve [econstructor; eauto using inclusion_cons].
  Admitted.

  Lemma weakening_empty : forall Δ' T K,
      [] |-* T : K ->
      Forall (fun X => lookup X Δ' = None) (Ty.btv T) ->
      kctx_wf Δ' ->
      Δ' |-* T : K.
  Proof.
    intros.
    eapply weakening; eauto using inclusion_empty.
    constructor.
  Qed.

End Kinding.

Module Typing.

  Lemma kctx_wf__inclusion Δ Δ':
     inclusion Δ Δ' ->
     kctx_wf Δ' ->
     kctx_wf Δ.
  Proof.
    intros H_incl H_kctx.
    induction Δ.
    - admit.
    - unfold kctx_wf in *.
      inversion H_incl.
      simpl.

  Qed.

  Definition P_has_type Δ Gamma t T : Prop :=
    forall Δ' Gamma',
      kctx_wf Δ ->
      kctx_wf Δ' ->
      inclusion Δ Δ' ->
      inclusion Gamma Gamma' ->
      Δ' ,, Gamma' |-+ t : T.

  Definition P_constructor_well_formed Δ c T : Prop :=
    forall Δ',
      kctx_wf Δ ->
      kctx_wf Δ' ->
      inclusion Δ Δ' ->
      Δ' |-ok_c c : T.

  Definition P_bindings_well_formed_nonrec Δ Gamma bs : Prop :=
    forall Δ' Gamma',
      kctx_wf Δ ->
      kctx_wf Δ' ->
      inclusion Δ Δ' ->
      inclusion Gamma Gamma' ->
      Δ' ,, Gamma' |-oks_nr bs.

  Definition P_bindings_well_formed_rec Δ Gamma bs : Prop :=
    forall Δ' Gamma',
      kctx_wf Δ ->
      kctx_wf Δ' ->
      inclusion Δ Δ' ->
      inclusion Gamma Gamma' ->
      Δ' ,, Gamma' |-oks_r bs.

  Definition P_binding_well_formed Δ Gamma b : Prop :=
    forall Δ' Gamma',
      kctx_wf Δ ->
      kctx_wf Δ' ->
      inclusion Δ Δ' ->
      inclusion Gamma Gamma' ->
      Δ' ,, Gamma' |-ok_b b.

  #[export] Hint Unfold
    P_has_type
    P_constructor_well_formed
    P_bindings_well_formed_nonrec
    P_bindings_well_formed_rec
    P_binding_well_formed
    : core.

  Lemma weakening :
    (forall Δ Gamma t T, Δ ,, Gamma |-+ t : T -> P_has_type Δ Gamma t T) /\
    (forall Δ Gamma bs, Δ ,, Gamma |-oks_nr bs -> P_bindings_well_formed_nonrec Δ Gamma bs) /\
    (forall Δ Gamma bs, Δ ,, Gamma |-oks_r bs -> P_bindings_well_formed_rec Δ Gamma bs) /\
    (forall  Δ Gamma b, Δ ,, Gamma |-ok_b b -> P_binding_well_formed Δ Gamma b).
  Proof with eauto using Kinding.weakening, inclusion_cons, inclusion_append.
    apply has_type__multind with
      (P := P_has_type)
      (P0 := P_constructor_well_formed)
      (P1 := P_bindings_well_formed_nonrec)
      (P2 := P_bindings_well_formed_rec)
      (P3 := P_binding_well_formed).
    all: intros; autounfold.
    all: try (intros Δ'_0 Gamma'_0 HinclD HinclG).
    all: try (intros Δ'_0 HinclD).
    all: try solve [econstructor; subst; eauto using Kinding.weakening, inclusion_cons, inclusion_append].
    - (* Ty_Forall *)
      unfold P_has_type in *.
      econstructor...
      apply H0...
      unfold P_has_type in *.
        simpl.
        admit. (* holds via inclusion *)
      +
        admit. (* holds via inclusion *)
    - (* LetNonRec *)
      admit. (* TODO: add constraints in typing rules of LetRec and LetNonRec *)
    - (* LetRec *)
      admit. (* TODO: add constraints in typing rules of LetRec and LetNonRec *)
    - (* oks_nr *)
      admit. (* TODO: add constraints in typing rules of LetRec and LetNonRec *)
    - (* W Data*)
      econstructor...
      + subst.
        intros.
        eapply H7...
        all: admit. (* TODO: add constraints in typing rules of LetRec and LetNonRec *)
      + subst...
  Admitted.

  Lemma weakening_empty : forall Δ Gamma t T,
      kctx_wf Δ ->
      [] ,, [] |-+ t : T ->
      Δ ,, Gamma |-+ t : T.
  Proof.
    intros Δ Gamma t H_NoDup T Ht.
    apply weakening in Ht.
    unfold P_has_type in Ht.
    apply Ht.
    - unfold kctx_wf in *. auto using NoDup.
    - assumption.
    - apply inclusion_empty.
    - apply inclusion_empty.
  Qed.

  Corollary weakening_term Δ Δ' Gamma Gamma' t T
    (incl_Δ : inclusion Δ Δ')
    (incl_Gamma : inclusion Gamma Gamma') :
      kctx_wf Δ ->
      kctx_wf Δ' ->
      Δ ,, Gamma |-+ t : T ->
      Δ' ,, Gamma' |-+ t : T.
  Proof.
    intros.
    eapply weakening.
    all: eassumption.
  Qed.

End Typing.
