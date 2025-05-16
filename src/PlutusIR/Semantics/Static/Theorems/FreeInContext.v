Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
Require Import Lists.List.
Import ListNotations.

Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.In_Auxiliary.
Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.

Require Import Coq.Program.Equality.

Module Ty.

  Lemma free_in_context : forall Delta T K,
    Delta |-* T : K ->
    forall X,
      Ty.appears_free_in X T ->
      exists K', lookup X Delta = Datatypes.Some K'.
  Proof with eauto.
    induction 1.
    all: intros X0 Hafi.
    all: try solve [inversion Hafi; subst; eauto].
    - inversion Hafi. subst.
      eapply IHhas_kind in H5.
      rewrite lookup_neq in H5...
    - inversion Hafi. subst.
      eapply IHhas_kind in H5.
      rewrite lookup_neq in H5...
  Qed.

  Corollary kindable_empty__closed : forall T K,
      [] |-* T : K ->
      Ty.closed T.
  Proof with eauto.
    intros. unfold Ty.closed.
    intros x H1.
    eapply free_in_context in H1...
    destruct H1 as [T' C]...
    discriminate C.
  Qed.

End Ty.

Module Term.

  Definition P_has_type (Delta : list (string * kind)) (Gamma : list (string * ty)) (t : term) (T : ty) :=
    forall x,
      Term.appears_free_in x t ->
      exists T', lookup x Gamma = Datatypes.Some T'.

  Definition P_constructor_well_formed (Delta : list (string * kind)) (c : vdecl) (T : ty) :=
    Delta |-ok_c c : T.

  Definition P_bindings_well_formed_nonrec (Delta : list (string * kind)) (Gamma : list (string * ty)) (bs : list binding) :=
    forall x,
      Term.appears_free_in__bindings_nonrec x bs ->
      exists T', lookup x Gamma = Datatypes.Some T'.

  Definition P_bindings_well_formed_rec  (Delta : list (string * kind)) (Gamma : list (string * ty)) (bs : list binding) :=
    forall x,
      Term.appears_free_in__bindings_rec x bs ->
      exists T', lookup x Gamma = Datatypes.Some T'.

  Definition P_binding_well_formed (Delta : list (string * kind)) (Gamma : list (string * ty)) (rec : recursivity) (b : binding) :=
    forall x,
      Term.appears_free_in__binding x b ->
      exists T', lookup x Gamma = Datatypes.Some T'.

  #[export] Hint Unfold
    P_has_type
    P_constructor_well_formed
    P_bindings_well_formed_nonrec
    P_bindings_well_formed_rec
    P_binding_well_formed
    : core.

  Lemma free_in_context :
      (forall Delta Gamma t T, Delta ,, Gamma |-+ t : T -> P_has_type Delta Gamma t T) /\
      (forall Delta Gamma bs, Delta ,, Gamma |-oks_nr bs -> P_bindings_well_formed_nonrec Delta Gamma bs) /\
      (forall Delta Gamma bs, Delta ,, Gamma |-oks_r bs -> P_bindings_well_formed_rec Delta Gamma bs) /\
      (forall Delta Gamma rec b, Delta ,, Gamma |-ok_b rec # b -> P_binding_well_formed Delta Gamma rec b).
  Proof with eauto.
    apply has_type__multind with
      (P := P_has_type)
      (P0 := P_constructor_well_formed)
      (P1 := P_bindings_well_formed_nonrec)
      (P2 := P_bindings_well_formed_rec)
      (P3 := P_binding_well_formed).
    all: intros; autounfold.
    all: try solve [econstructor; eauto].
    all: try (intros x0 Hafi).
    all: try solve [inversion Hafi; subst; eauto].
    - (* T_LamAbs *)
      inversion Hafi. subst.
      eapply H2 in H8...
      rewrite lookup_neq in H8...
    - (* TyAbs *)
      unfold P_has_type in H0.
      assert (Term.appears_free_in x0 t).
      {
        inversion Hafi; subst; auto.
      }
      specialize (H0 x0 H3) as [T' Hlookup].
      eapply drop_ty_var__lookup_some in Hlookup as [T'' Hl'']; eauto.
      eapply drop_ty_var__lookup_some; eauto.
    - (* T_Let *)
      inversion Hafi.
      + subst.
        eapply H5 in H13...
        apply notIn_bvbs_bindsG in H11.
        eapply notIn__map_normalise in H11...
        rewrite notIn__lookup_append in H13...
      + subst.
        eapply H3 in H10...
    - (* T_LetRec *)
      inversion Hafi.
      + subst.
        eapply H7 in H15...
        apply notIn_bvbs_bindsG in H13.
        eapply notIn__map_normalise in H13...
        rewrite notIn__lookup_append in H15...
      + subst.
        eapply H5 in H14...
        apply notIn_bvbs_bindsG in H13.
        eapply notIn__map_normalise in H13...
        rewrite notIn__lookup_append in H14...
    - (* W_ConsB_NonRec *)
      inversion Hafi.
      + subst.
        apply H0...
      + subst.
        apply notIn_bvb_bindsG in H7.
        eapply notIn__map_normalise in H7...
        erewrite <- notIn__lookup_append...
Qed.

End Term.

Module Annotation.

  Definition P_has_type (Delta : list (string * kind)) (Gamma : list (string * ty)) (t : term) (T : ty) :=
    forall X,
      Annotation.appears_free_in X t ->
      exists K', lookup X Delta = Datatypes.Some K'.

  Definition P_constructor_well_formed (Delta : list (string * kind)) (c : vdecl) (T : ty) :=
    forall X,
      Annotation.appears_free_in__constructor X c ->
      exists K', lookup X Delta = Datatypes.Some K'.

  Definition P_bindings_well_formed_nonrec (Delta : list (string * kind)) (Gamma : list (string * ty)) (bs : list binding) :=
    forall X,
      Annotation.appears_free_in__bindings_nonrec X bs ->
      exists K', lookup X Delta = Datatypes.Some K'.

  Definition P_bindings_well_formed_rec (Delta : list (string * kind)) (Gamma : list (string * ty)) (bs : list binding) :=
    forall X,
      Annotation.appears_free_in__bindings_rec X bs ->
      exists K', lookup X Delta = Datatypes.Some K'.

  Definition P_binding_well_formed (Delta : list (string * kind)) (Gamma : list (string * ty)) (rec : recursivity) (b : binding) :=
    forall X,
      Annotation.appears_free_in__binding X b ->
      exists K', lookup X Delta = Datatypes.Some K'.


  #[export] Hint Unfold
    P_has_type
    P_constructor_well_formed
    P_bindings_well_formed_nonrec
    P_bindings_well_formed_rec
    P_binding_well_formed
    : core.

  Lemma free_in_context :
      (forall Delta Gamma t T, Delta ,, Gamma |-+ t : T -> P_has_type Delta Gamma t T) /\
      (forall Delta Gamma bs, Delta ,, Gamma |-oks_nr bs -> P_bindings_well_formed_nonrec Delta Gamma bs) /\
      (forall Delta Gamma bs, Delta ,, Gamma |-oks_r bs -> P_bindings_well_formed_rec Delta Gamma bs) /\
      (forall Delta Gamma rec b, Delta ,, Gamma |-ok_b rec # b -> P_binding_well_formed Delta Gamma rec b).
  Proof with (eauto using Ty.free_in_context).
    apply has_type__multind with
      (P := P_has_type)
      (P0 := P_constructor_well_formed)
      (P1 := P_bindings_well_formed_nonrec)
      (P2 := P_bindings_well_formed_rec)
      (P3 := P_binding_well_formed).
    all: intros; autounfold.
    all: try (intros x0 Hafi).
    all: try solve [inversion Hafi; subst; eauto using Ty.free_in_context].
    - (* T_TyAbs *)
      dependent destruction Hafi.
      subst.
      eapply H0 in Hafi...
      rewrite lookup_neq in Hafi...
    - (* T_Let*)
      inversion Hafi.
      + subst.
        eapply H5 in H12...
        apply notIn_btvbs_bindsD in H10.
        rewrite notIn__lookup_append in H12...
      + subst.
        eapply H3 in H9...
    - (* T_LetRec *)
      inversion Hafi.
      + subst.
        eapply H7 in H14...
        apply notIn_btvbs_bindsD in H12.
        rewrite notIn__lookup_append in H14...
      + subst.
        eapply H5 in H13...
        apply notIn_btvbs_bindsD in H12.
        rewrite notIn__lookup_append in H13...
    - (* W_Con *)
      inversion Hafi. subst.
      rewrite <- H4 in H.
      inversion H. subst.
      destruct H5 as [U [HIn__U Hafi__U]].
      eapply Ty.free_in_context...
    - (* W_ConsB_NonRec *)
      inversion Hafi.
      + subst.
        apply H0...
      + subst.
        apply notIn_btvb_bindsD in H6.
        erewrite <- notIn__lookup_append...
    - (* W_Data *)
      inversion Hafi. subst.
      inversion H10. subst.
      destruct H12 as [c [HIn__c Hafi__c]].
      erewrite <- notIn__lookup_append...
      simpl in H7.
      simpl in H8.
      destruct rec.
      + specialize (H8 c HIn__c x0 Hafi__c) as [K' Hl_K].
        exists K'.
        eapply inclusion_unfold; eauto.
        apply inclusion_append.
        apply drop_Δ'__inclusion.
      + eapply H8...
  Qed.

End Annotation.

Corollary typable_empty__closed : forall t T,
    [] ,, [] |-+ t : T ->
    closed t.
Proof with eauto.
  intros. unfold closed.
  split.
  - intros x H1.
    eapply Term.free_in_context in H1...
    destruct H1 as [T' C]...
    discriminate C.
  - intros X H1.
    eapply Annotation.free_in_context in H1...
    destruct H1 as [K' C]...
    discriminate C.
Qed.
