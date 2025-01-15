Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.

Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.In_Auxiliary.
Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.

Require Import Coq.Lists.List.

Local Open Scope string_scope.



Module Kinding.

  Lemma context_invariance : forall Delta Delta' T K,
      Delta |-* T : K ->
      (forall X, Ty.appears_free_in X T -> lookup X Delta = lookup X Delta') ->
      Delta' |-* T : K.
  Proof with auto.
    intros Delta Delta' T K HK.
    generalize dependent Delta'.
    induction HK; intros; try solve [econstructor; eauto].
    - apply K_Var.
      rewrite <- H0...
    - (* K_Forall *)
      apply K_Forall.
      apply IHHK.
      intros.
      destruct (X =? X0) eqn:Heqb.
      + apply eqb_eq in Heqb.
        subst.
        rewrite lookup_eq.
        rewrite lookup_eq.
        reflexivity.
      + apply eqb_neq in Heqb.
        rewrite lookup_neq...
        rewrite lookup_neq...
    - (* K_Lam *)
      apply K_Lam.
      apply IHHK.
      intros.
      destruct (X =? X0) eqn:Heqb.
      + apply eqb_eq in Heqb.
        subst.
        rewrite lookup_eq.
        rewrite lookup_eq.
        reflexivity.
      + apply eqb_neq in Heqb.
        rewrite lookup_neq...
        rewrite lookup_neq...
  Qed.

End Kinding.

Module Typing.

  Definition P_has_type (Delta : list (string * kind)) (Gamma : list (string * ty)) (t : term) (T : ty) :=
    forall Gamma',
      (forall x, Term.appears_free_in x t -> lookup x Gamma = lookup x Gamma') ->
      Delta ,, Gamma' |-+ t : T.

  Definition P_constructor_well_formed (Delta : list (string * kind)) (c : vdecl) (T : ty) :=
    Delta |-ok_c c : T.

  Definition P_bindings_well_formed_nonrec (Delta : list (string * kind)) (Gamma : list (string * ty)) (bs : list binding) :=
    forall Gamma',
      (forall x, Term.appears_free_in__bindings_nonrec x bs -> lookup x Gamma = lookup x Gamma') ->
      Delta ,, Gamma' |-oks_nr bs.

  Definition P_bindings_well_formed_rec (Delta : list (string * kind)) (Gamma : list (string * ty)) (bs : list binding) :=
    forall Gamma',
      (forall x, Term.appears_free_in__bindings_rec x bs -> lookup x Gamma = lookup x Gamma') ->
      Delta ,, Gamma' |-oks_r bs.

  Definition P_binding_well_formed (Delta : list (string * kind)) (Gamma : list (string * ty)) (b : binding) :=
    forall Gamma',
      (forall x, Term.appears_free_in__binding x b -> lookup x Gamma = lookup x Gamma') ->
      Delta ,, Gamma' |-ok_b b.

  #[export] Hint Unfold
    P_has_type
    P_constructor_well_formed
    P_bindings_well_formed_nonrec
    P_bindings_well_formed_rec
    P_binding_well_formed
    : core.

  Theorem context_invariance :
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
    all: intros; autounfold; intros.
    all: try solve [econstructor; eauto].

    - (* T_Var *)
      eapply T_Var...
      rewrite <- H1; auto.
    - (* T_LamAbs *)
      apply T_LamAbs...
      apply H2.
      intros.
      destruct (x =? x0) eqn:Heqb.
      + apply eqb_eq in Heqb.
        subst.
        rewrite lookup_eq.
        rewrite lookup_eq.
        reflexivity.
      + apply eqb_neq in Heqb.
        rewrite lookup_neq; auto.
        rewrite lookup_neq; auto.
    - (* Ty_Forall *)
      econstructor; auto.
      (* Suppose X in Γ_ftv of Gamma', then it must be in one of its values, say val1
        val1 has a corresponding key, say "x"
        Then by H2, we know lookup x Γ = lookup x Γ'

        We just found val1 = lookup x Γ'
        So lookup x Γ = val1.

        So X in ftv val1. So X in Γ_ftv Γ.

        Contradiction.
      *)
      admit.
    - (* Ty_Forall_ren*)
      econstructor; auto.
      + admit.
      + unfold P_has_type in H3.
        specialize (H3 Gamma').
        eapply H3.
        (* Term.appears_free_in x (TyAbs X K t) is a superset of
          Term.appears_free_in x (rename_ty X X' t) ?

          what about X', what if that appears free in TyAbs X K t? It cannot by X' not in tv t
          also X is not free in TyAbs X K t, so it does not matter that we rename it away.
        *)
        intros.
        admit.

    - (* T_Let *)
      subst.
      eapply T_Let...
      apply H5.
      intros.
      assert ({In x (bvbs bs)} + {~ In x (bvbs bs)}) by eauto using in_dec, string_dec.
      destruct H1.
      + apply In_bvbs_bindsG in i.
        eapply In__map_normalise in i...
        apply In__lookup_append...
      + apply lookup_append_cong...
    - (* T_LetRec *)
      subst.
      eapply T_LetRec...
      + apply H3.
        intros.
        assert ({In x (bvbs bs)} + {~ In x (bvbs bs)}) by eauto using in_dec, string_dec.
        destruct H1.
        * apply In_bvbs_bindsG in i.
          eapply In__map_normalise in i...
          apply In__lookup_append...
        * apply lookup_append_cong...
      + apply H5.
        intros.
        assert ({In x (bvbs bs)} + {~ In x (bvbs bs)}) by eauto using in_dec, string_dec.
        destruct H1.
        * apply In_bvbs_bindsG in i.
          eapply In__map_normalise in i...
          apply In__lookup_append...
        * apply lookup_append_cong...
    - (* W_ConsB_NonRec *)
      eapply W_ConsB_NonRec...
      eapply H3.
      intros.
      assert ({In x (bvb b)} + {~ In x (bvb b)}) by eauto using in_dec, string_dec.
      destruct H6.
      + apply In_bvb_bindsG in i.
        eapply In__map_normalise in i...
        apply In__lookup_append...
      + apply lookup_append_cong...
  Admitted.

End Typing.
