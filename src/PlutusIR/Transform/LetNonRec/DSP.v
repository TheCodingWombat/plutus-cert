Require Import PlutusCert.PlutusIR.Transform.LetNonRec.Spec.
Require Import PlutusCert.PlutusIR.Transform.LetNonRec.SSP.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Misc.Axiom.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.

Import PlutusNotations.

Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.

Import Utf8_core.




(** * [CNR] is semantics preserving *)

(** ** Translation relation specific compatibility lemmas *)


Lemma compatibility_TermBind__desugar : forall Delta Gamma t t' Tn b bs fbs' tb tb' x Tb Tbn,
  Delta |-* Tb : Kind_Base ->
  normalise Tb Tbn ->
  forall Delta_ih Gamma_ih bsGn,
    b = TermBind Strict (VarDecl x Tb) tb ->
    Delta_ih = binds_Delta b ++ Delta ->
    map_normalise (binds_Gamma b) bsGn ->
    Gamma_ih = bsGn ++ Gamma ->
    LR_logically_approximate Delta_ih Gamma_ih (Let NonRec bs t) (fold_right apply t' fbs') Tn ->
    LR_logically_approximate Delta Gamma tb tb' Tbn ->
    LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (Apply (LamAbs x Tb (fold_right apply t' fbs')) tb') Tn.
Proof with eauto_LR.
  intros Delta Gamma t t' Tn b bs fbs' tb tb' x Tb Tbn.
  intros Hkind__Tb Hnorm__Tbn.
  intros Delta_ih Gamma_ih bsGn.
  intros Heq__b Heq__Delta_ih Hmapnorm__bsGn Heq__Gamma_ih IHLR__ih IHLR__tb.
  subst.

  destruct IHLR__ih as [Htyp__ih [Htyp__ih' IH__ih]].
  destruct IHLR__tb as [Htyp__tb [Htyp__tb' IH__tb]].

  split. {
    inversion Htyp__ih. subst.
    rewrite <- append_flatten in H7.

    eapply T_Let...
    - unfold flatten.
      simpl.
      simpl in Hmapnorm__bsGn.
      rewrite List.concat_app.
      eapply map_normalise__app'...
    - rewrite <- app_assoc...
  }

  split. {
    eapply T_Apply...
    eapply T_LamAbs...
    simpl in Hmapnorm__bsGn.
    inversion Hmapnorm__bsGn. subst.
    inversion H3. subst.
    eapply normalisation__deterministic in Hnorm__Tbn...
    subst...
  }

  intros k rho env env' HRD HRG.

  rewrite msubstA_LetNonRec.
  rewrite msubstA_BindingsNonRec_cons.
  rewrite msubstA_TermBind.
  rewrite msubst_LetNonRec.
  rewrite msubst_bnr_cons.
  rewrite msubst_TermBind.

  rewrite msubstA_Apply.
  rewrite msubstA_LamAbs.
  rewrite msubst_Apply.
  rewrite msubst_LamAbs.

  autorewrite with RC.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  clear Hev__e_f. rename H3 into Hev__e_f.
  inversion Hev__e_f; subst.
  - clear Hev__e_f.
    rename v1 into vb.
    rename j1 into jb.
    rename H6 into Hev__vb.
    rename H7 into Hnerr__vb.
    rename H8 into Hev__e_f.

    assert (HRC__tb :
      RC k Tbn rho
        (msubst env (msubstA (msyn1 rho) tb))
        (msubst env' (msubstA (msyn2 rho) tb'))
    )...
    clear IH__tb.

    eapply RC_to_RV with (j := jb) (e_f := vb) in HRC__tb as temp...
    destruct temp as [vb' [jb' [Hev__vb' HRV__vb]]].
    clear Hev__vb.
    clear HRC__tb.

    assert (HRC__ih :
      RC (k - jb - 1) Tn rho
        <{ /[ (x, vb) :: env /] ( /[[ msyn1 rho /] {Let NonRec bs t} ) }>
        <{ /[ (x, vb') :: env' /] ( /[[ msyn2 rho /] {fold_right apply t' fbs'} ) }>
    ). {
      apply IH__ih.
      - assumption.
      - assert (closed vb). eapply RV_closed_1...
        assert (closed vb'). eapply RV_closed_2...
        replace vb with (msubstA (msyn1 rho) vb) by (eapply msubstA_closed; eauto).
        replace vb' with (msubstA (msyn2 rho) vb') by (eapply msubstA_closed; eauto).
        simpl in Hmapnorm__bsGn.
        inversion Hmapnorm__bsGn. subst.
        replace Tn0 with Tbn...
        apply RG_cons.
        + apply RV_monotone with (k := k - jb) (ck := Delta)...
          rewrite msubstA_closed...
          rewrite msubstA_closed...
        + eapply normalise_to_normal...
        + apply not_is_error_msubstA.
          assumption.
        + apply RG_monotone with (k := k) (ck := Delta)...
          inversion H5...
    }
    clear IH__ih.

    apply RC_to_RV with (j := j2) (e_f := e_f) in HRC__ih as temp...
    * destruct temp as [e'_f [j2' [Hev__e'_f HRV0]]].
      clear Hev__e_f.

      eexists. eexists.
      split. {
        eapply E_Apply...
        - inversion 1. repeat (match goal with | H : applied_builtin _ _ _ |- _ => inversion_clear H end).
        - eapply E_LamAbs.
        - eapply RV_error in HRV__vb as temp...
          destruct temp as [ [Herr Herr'] | [Hnerr Hnerr']]...
        - rewrite <- subst_msubst...
          + eapply RV_closed_2...
          + eapply RG_env_closed_2...
      }

      split... eapply RV_typable_empty_1...
      split... eapply RV_typable_empty_2...

      eapply RV_condition...
      eapply RV_monotone...
    * rewrite msubstA_LetNonRec.
      rewrite msubst_LetNonRec.

      apply E_Let.

      simpl.
      simpl in Hev__e_f.

      rewrite <- msubst_bnr__bound_vars in Hev__e_f.
      rewrite <- msubstA_bnr__bvbs in Hev__e_f.


      (* TODO: Duplication from compatibility lemma TermBind *)
      destruct (existsb (eqb x) (bvbs bs)) eqn:Hexb. {
        assert (closed vb). eapply RV_closed_1...
        assert (closed vb'). eapply RV_closed_2...
        apply RG_env_closed in HRG as Hclss...
        destruct Hclss as [Hcls__env Hcls__env'].
        rewrite <- subst_bnr__msubst_bnr' in Hev__e_f...
        replace (concat (map bvb <{ /[[ msyn1 rho /][bnr] bs }>)) with
          (bvbs <{ /[[ msyn1 rho /][bnr] bs }>) in Hev__e_f...

        unfold btvbs in Hev__e_f.
        simpl in Hev__e_f.
        rewrite <- msubstA_bnr__bvbs.
        rewrite <- msubstA_bnr__bvbs in Hev__e_f.

        apply existsb_exists in Hexb.
        destruct Hexb as [y [HIn Heqb]].
        apply eqb_eq in Heqb as Heq.
        subst.
        rewrite In__mdrop...
        rewrite subst_bnr__msubst_bnr' in Hev__e_f...
        rewrite <- subst_bnr__msubst_bnr in Hev__e_f...
        rewrite In__mdrop_drop in Hev__e_f...
      } {

        assert (closed vb). eapply RV_closed_1...
        assert (closed vb'). eapply RV_closed_2...
        apply RG_env_closed in HRG as Hclss...
        destruct Hclss as [Hcls__env Hcls__env'].
        rewrite <- subst_bnr__msubst_bnr in Hev__e_f...
        replace (concat (map bvb <{ /[[ msyn1 rho /][bnr] bs }>)) with
          (bvbs <{ /[[ msyn1 rho /][bnr] bs }>) in Hev__e_f...

        unfold btvbs in Hev__e_f.
        simpl in Hev__e_f.
        rewrite <- msubstA_bnr__bvbs.
        rewrite <- msubstA_bnr__bvbs in Hev__e_f.

        apply Util.existsb_nexists in Hexb.
        rewrite not_In__mdrop.
        - replace (concat (map btvb bs)) with (btvbs bs) in Hev__e_f...
          rewrite <- drop_mdrop in Hev__e_f.
          rewrite <- subst_msubst in Hev__e_f...
          + eapply RG_env_closed_1.
            eapply RG_mdrop...
            eauto_LR.
        - intros Hcon.
          apply Hexb.
          exists x.
          rewrite eqb_refl.
          eauto.
      }
  - clear Hev__e_f.
    rename j1 into jb.
    rename H6 into Hev__vb.

    assert (HRC__tb :
      RC k Tbn rho
        (msubst env (msubstA (msyn1 rho) tb))
        (msubst env' (msubstA (msyn2 rho) tb'))
    )...
    clear IH__tb.

    apply RC_to_RV with (j := jb) (e_f := Error T') in HRC__tb as temp...
    destruct temp as [e'_f [j' [Hev__e'_f HRV__vb]]].

    eapply RV_error in HRV__vb as temp...

    destruct temp as [ [Hnerr Hnerr'] | [Herr Herr']].
    + exfalso. eapply Hnerr. econstructor.
    + inversion Herr'. subst.

      eexists. eexists.
      split. eapply E_Error_Apply2...

      split. {
        inversion Htyp__ih. subst.
        simpl in H9.
        eapply closing_preserves_kinding_1 in H9 as H10...
        eapply strong_normalisation in H10 as H11...
        destruct H11.

        eexists. split...
      }

      split. {
        inversion Htyp__ih. subst.
        simpl in H9.
        eapply closing_preserves_kinding_2 in H9 as H10...
        eapply strong_normalisation in H10 as H11...
        destruct H11.

        eexists. split...
      }
      right...
Qed.

(** ** Predicates *)

Definition P_has_type Delta Gamma t T : Prop :=
  forall t',
    CNR_Term t t' ->
    LR_logically_approximate Delta Gamma t t' T.

Definition P_constructor_well_formed Delta c Tr : Prop := Delta |-ok_c c : Tr.

Definition P_bindings_well_formed_nonrec Delta Gamma bs : Prop :=
  (
    forall bs',
      Compat.Compat_Bindings CNR_Term bs bs' ->
      forall Delta_t Gamma_t bsGn t t' Tn,
        Delta_t = flatten (List.map binds_Delta bs) ++ Delta  ->
        map_normalise (flatten (List.map binds_Gamma bs)) bsGn ->
        Gamma_t = bsGn ++ Gamma ->
        Delta |-* Tn : Kind_Base ->
        LR_logically_approximate Delta_t Gamma_t t t' Tn ->
        LR_logically_approximate Delta Gamma (Let NonRec bs t) (Let NonRec bs' t') Tn
  ) /\ (
    forall fbs',
      CNR_Bindings bs fbs' ->
      forall Delta_t Gamma_t bsGn t t' Tn,
        Delta_t = flatten (List.map binds_Delta bs) ++ Delta  ->
        map_normalise (flatten (List.map binds_Gamma bs)) bsGn ->
        Gamma_t = bsGn ++ Gamma ->
        Delta |-* Tn : Kind_Base ->
        LR_logically_approximate Delta_t Gamma_t t t' Tn ->
        LR_logically_approximate Delta Gamma (Let NonRec bs t) (fold_right apply t' fbs') Tn
  ).

Definition P_bindings_well_formed_rec Delta Gamma bs1 : Prop := Delta ,, Gamma |-oks_r bs1.

Definition P_binding_well_formed Delta Gamma b : Prop :=
  (
    forall b',
      Compat.Compat_Binding CNR_Term b b' ->
      forall Delta_t Gamma_t bsGn t t' Tn bs bs',
        Delta_t = binds_Delta b ++ Delta ->
        map_normalise (binds_Gamma b) bsGn ->
        Gamma_t = bsGn ++ Gamma ->
        Delta |-* Tn : Kind_Base ->
        LR_logically_approximate Delta_t Gamma_t (Let NonRec bs t) (Let NonRec bs' t') Tn ->
        LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t') Tn
  ) /\ (
    forall fb',
      CNR_Binding b fb' ->
      forall Delta_t Gamma_t bsGn t t' Tn bs fbs',
        Delta_t = binds_Delta b ++ Delta ->
        map_normalise (binds_Gamma b) bsGn ->
        Gamma_t = bsGn ++ Gamma ->
        Delta |-* Tn : Kind_Base ->
        LR_logically_approximate Delta_t Gamma_t (Let NonRec bs t) (fold_right apply t' fbs') Tn ->
        LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (fold_right apply t' (fb' :: fbs')) Tn
  ).

#[export] Hint Unfold
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed : core.

Ltac inv_CNR :=
  match goal with
  | H : CNR_Term _ _ |- _ => inversion H; subst
  | H : CNR_Bindings _ _ |- _ => inversion H; subst
  | H : CNR_Binding _ _ |- _ => inversion H; subst
  end.

Ltac inv_Compat :=
  match goal with
    | H : Compat.Compat _ _ _ |- _ => inversion H; subst
    | H : Compat.Compat_Bindings _ _ _ |- _ => inversion H; subst
    | H : Compat.Compat_Binding _ _ _ |- _ => inversion H; subst
  end.

(** ** The main theorem *)

Theorem CNR_Term__DSP : forall Delta Gamma e T,
    Delta ,, Gamma |-+ e : T ->
    P_has_type Delta Gamma e T.
Proof with (eauto_LR || eauto with DSP_compatibility_lemmas).
  apply has_type__ind with
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).

  all : intros; autounfold; intros; subst.
  all: try solve [ inv_CNR; eauto with DSP_compatibility_lemmas typing].
  all : try solve [eauto with typing].
  - (* T_TyAbs *)
    admit.
  - (* T_Let *)
    inv_CNR...
    + eapply H3...

  - (* W_NilB_NonRec *)
    split. all: intros. all: subst.
    + inv_Compat.
      inversion H1...
    + inv_CNR.
      match goal with
        | H : map_normalise _ _ |- _ => inversion H; subst; simpl in H
      end.
      eapply compatibility_LetNonRec_Nil'...
  - (* W_ConsB_NonRec *)
    split. all: intros. all: subst.
    +
      match goal with
        | H : map_normalise _ _ |- _ =>
            rewrite flatten_app in H;
            apply map_normalise__app in H;
            destruct H as [l1n [l2n [Hmn__l1n [Hmn__l2n Heq]]]];
            subst
      end.
      eapply map_normalise__deterministic in H1...
      subst.

      inv_Compat.

      eapply H0...
      eapply H3...
      * eapply Kinding.weakening; eauto.
        destruct b.
        -- simpl. eapply inclusion_refl.
        -- simpl. destruct t0. simpl.
            unfold inclusion.
            intros.
            destruct (b =? x)%string eqn:Heqb.
            ++ eapply eqb_eq in Heqb as Heq.
                subst.
                assert (appears_bound_in_ann x (Let NonRec (TypeBind (TyVarDecl x k) t1 :: bs) t)) by eauto.
                eapply uniqueness' in H5.
                rewrite H5 in H1.
                inversion H5.
            ++ apply eqb_neq in Heqb as Hneq.
              simpl. rewrite Heqb...
        -- destruct d.
            simpl. destruct t0.
            simpl.
            unfold inclusion.
            intros.
            destruct (b0 =? x)%string eqn:Heqb.
            ++ eapply eqb_eq in Heqb as Heq.
                subst.
                assert (appears_bound_in_ann x (Let NonRec (DatatypeBind (Datatype (TyVarDecl x k) l b l0) :: bs) t)) by eauto.
                eapply uniqueness' in H5.
                rewrite H5 in H1.
                inversion H5.
            ++ apply eqb_neq in Heqb as Hneq.
               simpl. rewrite Heqb...
      * rewrite app_assoc.
        rewrite app_assoc.
        rewrite <- flatten_app...
    +
      match goal with
      | H : map_normalise _ _ |- _ =>
          rewrite flatten_app in H;
          apply map_normalise__app in H;
          destruct H as [l1n [l2n [Hmn__l1n [Hmn__l2n Heq]]]]
      end.
      subst.
      eapply map_normalise__deterministic in H1...
      subst.

      inversion H4. subst.

      eapply H0...
      eapply H3...
      * eapply Kinding.weakening; eauto.
        destruct b.
        -- simpl. eapply inclusion_refl.
        -- simpl. destruct t0. simpl.
            unfold inclusion.
            intros.
            destruct (b =? x)%string eqn:Heqb.
            ++ eapply eqb_eq in Heqb as Heq.
                subst.
                assert (appears_bound_in_ann x (Let NonRec (TypeBind (TyVarDecl x k) t1 :: bs) t)) by eauto.
                eapply uniqueness' in H5.
                rewrite H5 in H1.
                inversion H5.
            ++ apply eqb_neq in Heqb as Hneq.
               simpl. rewrite Heqb...
        -- destruct d.
            simpl. destruct t0.
            simpl.
            unfold inclusion.
            intros.
            destruct (b0 =? x)%string eqn:Heqb.
            ++ eapply eqb_eq in Heqb as Heq.
                subst.
                assert (appears_bound_in_ann x (Let NonRec (DatatypeBind (Datatype (TyVarDecl x k) l b l0) :: bs) t)) by eauto.
                eapply uniqueness' in H5.
                rewrite H5 in H1.
                inversion H5.
            ++ apply eqb_neq in Heqb as Hneq.
               simpl. rewrite Heqb...
      * rewrite app_assoc.
        rewrite app_assoc.
        rewrite <- flatten_app...

  - (* W_Term *)
    split. all: intros. all: subst.
    + inv_Compat...
    + inv_CNR.
      eapply compatibility_TermBind__desugar...
  - (* W_Type *)
    split. all: intros. all: subst.
    + inv_Compat...
    + inv_CNR.
  - (* W_Data *)
    split. all: intros. all: subst.
    + inv_Compat...
    + inv_CNR...
Admitted.


From PlutusCert Require Import Contextual.

Theorem CNR_Term__sem : ∀ t t',
    CNR_Term t t' ->
    ∀ Δ Γ T, Δ ,, Γ |- t ≃-ctx t' : T.
Admitted.
