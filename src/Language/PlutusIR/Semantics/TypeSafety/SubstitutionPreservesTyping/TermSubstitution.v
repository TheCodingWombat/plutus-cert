Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.

Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma append_extendT_shadow : forall ctx' x T U ctx,
    lookupT ctx' x = Datatypes.Some T ->
    Implementations.append ctx' (x |T-> U; ctx) = Implementations.append ctx' ctx.
Proof.
  intros.
  unfold Implementations.append.
  apply cong_eq.
  - reflexivity.
  - apply functional_extensionality.
    intros.
    simpl.
    destruct (lookupT ctx' x0) eqn:Hx0.
    + reflexivity.
    + assert (forall ctx' x x0, lookupT ctx' x = Datatypes.Some T -> lookupT ctx' x0 = None -> x <> x0). {
        intros.
        intros Hcon.
        subst.
        rewrite H0 in H1.
        inversion H1.
      }
      remember (H0 _ _ _ H Hx0).
      clear Heqn.
      rewrite update_neq; auto.
Qed.

Lemma append_extendT_permute : forall ctx' x U ctx,
    lookupT ctx' x = None ->
    Implementations.append ctx' (x |T-> U; ctx) = (x |T-> U; Implementations.append ctx' ctx).
Proof. 
  intros.
  unfold Implementations.append.
  apply cong_eq.
  - reflexivity.
  - apply functional_extensionality.
    intros.
    simpl.
    destruct (lookupT ctx' x0) eqn:Hx0.
    + assert (forall ctx' x x0 T, lookupT ctx' x = Datatypes.Some T -> lookupT ctx' x0 = None -> x <> x0). {
        intros.
        intros Hcon.
        subst.
        rewrite H0 in H1.
        inversion H1.
      }
      remember (H0 _ _ _ _ Hx0 H).
      clear Heqn.
      rewrite update_neq; auto.
      rewrite Hx0.
      reflexivity.
    + destruct (x =? x0) eqn:Heqb.
      * apply eqb_eq in Heqb as Heq.
        subst.
        rewrite update_eq.
        rewrite update_eq.
        reflexivity.
      * apply eqb_neq in Heqb as Hneq.
        rewrite update_neq; auto.
        rewrite update_neq; auto.
        rewrite Hx0.
        reflexivity.
Qed.


Lemma binds_binds_bound_vars : forall a x,
    List.In x (term_vars_bound_by_binding a) ->
    exists U, lookupT (binds a) x = Datatypes.Some U.
Proof.
  intros.
  destruct a.
  - simpl.
    destruct (getName v =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      exists (getTy v).
      apply update_eq.
    + apply eqb_neq in Heqb as Hneq.
      simpl in H.
      destruct v.
      simpl in H.
      destruct H.
      * apply Hneq in H.
        destruct H.
      * destruct H.
  - simpl in H.
    destruct t.
    inversion H.
  - simpl.
Admitted.

Lemma mapbinds_binds_bound_vars : forall bs x,
  List.In x (term_vars_bound_by_bindings bs) ->
  exists U, lookupT (flatten (List.map binds bs)) x = Datatypes.Some U.
Proof.
  induction bs.
  - intros.
    inversion H.
  - intros.
    unfold term_vars_bound_by_bindings in H.
    simpl in H.
    apply List.in_app_or in H.
    destruct H.
    + simpl.
      unfold flatten.
      simpl.
      rewrite concat_append.
      simpl. 
      destruct (lookupT (Implementations.concat (List.rev (List.map binds bs))) x).
      * exists t.
        reflexivity.
      * destruct (lookupT (binds a) x) eqn:Hlookup.
        -- exists t.
           reflexivity.
        -- apply binds_binds_bound_vars in H.
           destruct H. 
           rewrite H in Hlookup.
           inversion Hlookup.
    + simpl.
      unfold flatten.
      simpl.
      rewrite concat_append.
      simpl.
      destruct (lookupT (Implementations.concat (List.rev (List.map binds bs))) x) eqn:Hlookup.
      * exists t.
        reflexivity.
      * apply IHbs in H.
        destruct H.
        unfold flatten in H.
        rewrite H in Hlookup.
        inversion Hlookup.
Qed.

Lemma binds_unbinds_unbound_vars : forall a x,
    ~(List.In x (term_vars_bound_by_binding a)) ->
    lookupT (binds a) x = None.
Proof.
  intros.
  destruct a.
  - simpl.
    destruct (getName v =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      destruct v.
      exfalso.
      apply H.
      simpl.
      left.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      apply update_neq.
      assumption.
  - reflexivity.
  - simpl.
    destruct d.
    simpl.
    destruct (s =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      exfalso.
      apply H.
      simpl.
      destruct t.
      simpl.
      left.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      rewrite update_neq; auto.
      destruct  (lookupT
      (List.fold_right Implementations.append emptyContext
         (List.map
            (fun x0 : binderTyname * Ty => fst x0 |T-> snd x0; emptyContext)
            (List.map (constrBind (Datatype t l s l0)) l0))) x) eqn:E.
      * exfalso.
        apply H.
        simpl.
        destruct t.
        simpl.
        right.
Admitted.

Lemma mapbinds_unbinds_unbound_vars : forall bs x,
    ~(List.In x (term_vars_bound_by_bindings bs)) ->
    lookupT (flatten (List.map binds bs)) x = None.
Proof.
  induction bs.
  - intros.
    reflexivity.
  - intros.
    simpl.
    unfold flatten.
    simpl.
    rewrite concat_append.
    simpl.
    destruct (lookupT (Implementations.concat (List.rev (List.map binds bs))) x) eqn:Hlookup.
    + rewrite IHbs in Hlookup.
      * symmetry in Hlookup.
        assumption.
      * intros Hcon.
        apply H.
        unfold term_vars_bound_by_bindings.
        simpl.
        apply List.in_or_app.
        right.
        assumption.
    + destruct (lookupT (binds a) x) eqn:Hlookup'.
      * rewrite binds_unbinds_unbound_vars in Hlookup'.
        -- auto.
        -- intros Hcon.
           apply H.
           unfold term_vars_bound_by_bindings.
           simpl.
           apply List.in_or_app.
           left.
           assumption.
      * reflexivity.
Qed.

Lemma context_invariance_T__constructor_well_formed : forall ctx_T' ctx_T ctx_K c ,
  (ctx_K, ctx_T) |-ok_c c ->
  (ctx_K, ctx_T') |-ok_c c.
Proof.
  intros.
  inversion H. subst.
  apply W_Con.
  intros.
  apply H0.
  assumption.
Qed.

Definition P_Term (t : Term) :=
  forall ctx x U v T t',
    extendT x U ctx |-+ t : T ->
    emptyContext |-+ v : U ->
    substitute x v t t' ->
    ctx |-+ t' : T.
#[export] Hint Unfold P_Term : core.

Definition P_Binding (b : Binding) : Prop :=
  forall ctx x U v b',
    extendT x U ctx |-ok b ->
    emptyContext |-+ v : U ->
    substitute_binding x v b b' ->
    ctx |-ok b' /\ binds b = binds b'.
#[export] Hint Unfold P_Binding : core.

Lemma P_letnonrec : forall bs t ctx x U v bs' T t',
    P_Term t ->
    extendT x U ctx |-+ (Let NonRec bs t) : T ->
    emptyContext |-+ v : U ->
    Util.ForallP P_Binding bs ->
    substitute x v (Let NonRec bs t) (Let NonRec bs' t') ->
    ctx |-+ (Let NonRec bs' t') : T /\ List.map binds bs = List.map binds bs'.
Proof.
  induction bs; intros.
  - inversion H3. subst.
    split.
    + eapply T_Let.
      * reflexivity.
      * econstructor.
      * simpl.
        rewrite flatten_nil.
        rewrite append_emptyContext_l.
        eapply H; eauto.
        inversion H0. subst.
        eauto.
    + auto.
  - inversion H0. subst.
    inversion H8. subst.
    inversion H3. 
    + subst.
      apply binds_binds_bound_vars in H6.
      destruct H6 as [U' Hlu].
      split.
      * eapply T_Let.
        -- reflexivity.
        -- apply W_ConsB_NonRec.
           ++ eapply Util.ForallP_hd in H2.
              eapply H2; eauto.
           ++ eapply Util.ForallP_hd in H2.
              unfold P_Binding in H2.
              assert (binds a = binds b') by (eapply H2; eauto).
              rewrite <- H4.
              erewrite append_extendT_shadow in H9; eauto.
        -- simpl. 
Admitted.

Lemma P_letrec : forall bs t ctx x U v bs' T t',
    P_Term t ->
    extendT x U ctx |-+ (Let Rec bs t) : T ->
    emptyContext |-+ v : U ->
    Util.ForallP P_Binding bs ->
    substitute x v (Let Rec bs t) (Let Rec bs' t') ->
    ctx |-+ (Let Rec bs' t') : T /\ List.map binds bs = List.map binds bs'.
Proof. Admitted.

Lemma substitution_preserves_typing : 
  (forall t, P_Term t) /\ (forall b, P_Binding b).
Proof.
  intros.
  apply Term__multind with (P := P_Term) (Q := P_Binding).
  - intros. autounfold. intros.
    destruct rec.
    + inversion H3; subst. 
      all: eapply P_letnonrec; eauto.
    + inversion H3; subst.
      all: eapply P_letrec; eauto.
  - intros. autounfold. intros.
    inversion H1.
    + subst.
      inversion H.
      subst.
      inversion H4.
      rewrite update_eq in H3.
      inversion H3. subst. 
      eapply weakening_empty; eauto.
    + subst.
      apply T_Var.
      inversion H.
      subst.
      simpl in H5.
      rewrite update_neq in H5; auto.
  - (* TyAbs *) 
    intros. autounfold. intros.
    inversion H2. subst.
    inversion H0. subst.
    apply T_TyAbs.
    rewrite extendT_extendK_permute in H9.
    eapply H.
    + eauto.
    + eauto.
    + eauto.
  - (* LamAbs *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2.
    + subst.
      apply T_LamAbs.
      * rewrite extendT_shadow in H8.
        assumption.
      * destruct ctx.
        eauto.
    + subst.
      apply T_LamAbs.
      * eapply H.
        -- rewrite extendT_permute in H8; auto.
           apply H8.
        -- eassumption.
        -- assumption.
      * destruct ctx.
        eauto.
  - (* Apply *)
    intros. autounfold. intros.
    inversion H1. subst.
    inversion H3. subst.
    eapply T_Apply.
    + eapply H.
      * eassumption.
      * eassumption.
      * assumption.
    + eapply H0.
      * eassumption.
      * eassumption.
      * assumption.
  - (* Constant *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    apply T_Constant.
  - (* Builtin *) 
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    apply T_Builtin.
  - (* TyInst *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst.
    eapply T_TyInst.
    + eapply H.
      * eassumption.
      * eassumption.
      * eassumption.
    + destruct ctx.
      eauto.
    + eassumption.
    + eassumption.
  - (* Error *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    apply T_Error.
    destruct ctx.
    eauto.
  - (* IWrap *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst.
    eapply T_IWrap.
    + eassumption.
    + eapply H.
      * eassumption.
      * eassumption.
      * eassumption.
    + destruct ctx.
      eauto.
    + destruct ctx.
      eauto.
  - (* Unwrap *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst.
    eapply T_Unwrap.
    + eapply H.
      * eassumption.
      * eassumption.
      * assumption.
    + destruct ctx.
      eauto.
    + eassumption.

  - (* TermBind *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst. 
    split.
    + apply W_Term.
      * destruct ctx.
        eauto.
      * eapply H.
        -- eassumption.
        -- eassumption.
        -- assumption.
    + reflexivity. 
  - (* TypeBind *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    split. 
    + apply W_Type.
      destruct ctx.
      eauto.
    + reflexivity.
  - (* DatatypeBind *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    split.
    + eapply W_Data.
      * reflexivity.
      * intros.
        destruct ctx.
        eapply context_invariance_T__constructor_well_formed.
        eauto.
    + reflexivity.
Qed.

Corollary substitution_preserves_typing__Term : forall t ctx x U v T t',
    extendT x U ctx |-+ t : T ->
    emptyContext |-+ v : U ->
    substitute x v t t' ->
    ctx |-+ t' : T.
Proof. apply substitution_preserves_typing. Qed.

Corollary substitution_preserves_typing__Binding : forall b ctx x U v b',
    extendT x U ctx |-ok b ->
    emptyContext |-+ v : U ->
    substitute_binding x v b b' ->
    ctx |-ok b' /\ binds b = binds b'.
Proof. apply substitution_preserves_typing. Qed.