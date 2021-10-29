Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Typing.

Module Ty.

  Lemma free_in_context : forall Delta T K,
    Delta |-* T : K ->
    forall X,
      Ty.appears_free_in X T ->
      exists K', Delta X = Datatypes.Some K'.
  Proof with eauto.
    induction 1.
    all: intros X0 Hafi.
    all: try solve [inversion Hafi; subst; eauto].
    - inversion Hafi. subst.
      eapply IHhas_kind in H5.
      rewrite update_neq in H5...
    - inversion Hafi. subst.
      eapply IHhas_kind in H5.
      rewrite update_neq in H5...
  Qed.

End Ty.

Module Term.

  Definition P_has_type (Delta : Delta) (Gamma : Gamma) (t : Term) (T : Ty) :=
    forall x,
      Term.appears_free_in x t ->
      exists T', Gamma x = Datatypes.Some T'.
      
  Definition P_constructor_well_formed (Delta : Delta) (c : constructor) (T : Ty) :=
    Delta |-ok_c c : T.

  Definition P_bindings_well_formed_nonrec (Delta : Delta) (Gamma : Gamma) (bs : list Binding) :=
    forall x,
      Term.appears_free_in__bindings_nonrec x bs ->
      exists T', Gamma x = Datatypes.Some T'.

  Definition P_bindings_well_formed_rec  (Delta : Delta) (Gamma : Gamma) (bs : list Binding) :=
    forall x,
      Term.appears_free_in__bindings_rec x bs ->
      exists T', Gamma x = Datatypes.Some T'.

  Definition P_binding_well_formed (Delta : Delta) (Gamma : Gamma) (b : Binding) :=
    forall x,
      Term.appears_free_in__binding x b ->
      exists T', Gamma x = Datatypes.Some T'.

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
      (forall Delta Gamma b, Delta ,, Gamma |-ok_b b -> P_binding_well_formed Delta Gamma b).
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
      rewrite update_neq in H8...
    - (* T_Let *)
      inversion Hafi.
      + subst.
        eapply H5 in H12...
        admit.
      + subst.
        eapply H3 in H9...
    - (* T_LetRec *)
      inversion Hafi.
      + subst.
        eapply H5 in H12...
        admit.
      + subst.
        eapply H3 in H11...
        admit.
  Admitted.

End Term.

Module Annotation.

  Definition P_has_type (Delta : Delta) (Gamma : Gamma) (t : Term) (T : Ty) :=
    forall X,
      Annotation.appears_free_in X t ->
      exists K', Delta X = Datatypes.Some K'.
      
  Definition P_constructor_well_formed (Delta : Delta) (c : constructor) (T : Ty) :=
    forall X,
      Annotation.appears_free_in__constructor X c ->
      exists K', Delta X = Datatypes.Some K'.

  Definition P_bindings_well_formed_nonrec (Delta : Delta) (Gamma : Gamma) (bs : list Binding) :=
    forall X,
      Annotation.appears_free_in__bindings_nonrec X bs ->
      exists K', Delta X = Datatypes.Some K'.

  Definition P_bindings_well_formed_rec (Delta : Delta) (Gamma : Gamma) (bs : list Binding) :=
    forall X,
      Annotation.appears_free_in__bindings_rec X bs ->
      exists K', Delta X = Datatypes.Some K'.

  Definition P_binding_well_formed (Delta : Delta) (Gamma : Gamma) (b : Binding) :=
    forall X,
      Annotation.appears_free_in__binding X b ->
      exists K', Delta X = Datatypes.Some K'.

    
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
      (forall Delta Gamma b, Delta ,, Gamma |-ok_b b -> P_binding_well_formed Delta Gamma b).
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
      inversion Hafi.
      subst.
      eapply H0 in H5...
      rewrite update_neq in H5...
    - (* T_Let*)
      inversion Hafi.
      + subst.
        eapply H5 in H11...
        admit.
      + subst.
        eapply H3 in H8...
    - (* T_LetRec *)
      inversion Hafi.
      + subst.
        eapply H5 in H11...
        admit.
      + subst.
        eapply H3 in H10...
        admit.
  Admitted.

End Annotation.

Corollary typable_empty__closed : forall t T,
    empty ,, empty |-+ t : T ->
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
