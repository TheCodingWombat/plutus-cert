Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.SSP.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.ContextInvariance.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Progress.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Def.


Require Import Coq.Lists.List.

(** ** Multisubstitutions, multi-extensions, and instantiations *)

Definition env := list (name * Term).

Inductive msubst : env -> Term -> Term -> Prop :=
  | msubst_nil : forall t,
      msubst nil t t
  | msubst_cons : forall x s ss t t' t'',
      substitute x s t t' ->
      msubst ss t' t'' ->
      msubst ((x, s) :: ss) t t''
  .

Definition tass := list (name * Ty).

Fixpoint mupdate (Gamma : Context) (xts : tass) :=
  match xts with
  | nil => Gamma
  | ((x, v) :: xts') => extendT x v (mupdate Gamma xts')
  end. 

Fixpoint lookup {X:Type} (k : string) (l : list (name * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if String.eqb j k then Datatypes.Some x else lookup k l'
  end.

Fixpoint drop {X:Type} (n:string) (nxs:list (string * X)) : list (string * X) :=
  match nxs with
  | nil => nil
  | (n',x) :: nxs' => if String.eqb n' n then drop n nxs' else (n',x) :: (drop n nxs')
  end.

Inductive instantiation : tass -> env -> env -> Prop :=
  | V_nil : 
      instantiation nil nil nil
  | V_cons : forall x T v1 v2 c e1 e2,
      value v1 ->
      value v2 ->
      R T v1 v2 ->
      instantiation c e1 e2 ->
      instantiation ((x, T) :: c) ((x, v1) :: e1) ((x, v2) :: e2)
  . 



(** ** More substitution facts *)

Definition P_Term (t : Term) :=
  forall x,
    ~(appears_free_in x t) ->
    forall s t', 
      substitute x s t t' ->
      t' = t.

Definition P_Binding (b : Binding) :=
  forall x,
    ~(appears_free_in_binding x b) ->
    forall s b',
      substitute_binding x s b b' ->
      b' = b.

Definition P_Bindings_NonRec (bs : list Binding) :=
  Util.ForallT P_Binding bs ->
  forall x,
    ~(appears_free_in_bindings_nonrec x bs) ->
    forall s bs',
      substitute_bindings_nonrec x s bs bs' ->
      bs' = bs.

Lemma P_Bindings_NonRec__holds_definitionally : forall bs, P_Bindings_NonRec bs.
Proof.
  induction bs.
  - unfold P_Bindings_NonRec. intros.
    inversion H0. subst.
    reflexivity.
  - unfold P_Bindings_NonRec. intros.
    inversion H0.
    + subst.
      f_equal.
      apply Util.ForallT_hd in X.
      unfold P_Binding in X.
      apply X with x s.
      * intros Hcon.
        apply H.
        apply AFI_ConsB1_NonRec.
        assumption.
      * assumption.
    + subst.
      f_equal.
      * apply Util.ForallT_hd in X.
        unfold P_Binding in X.
        apply X with x s.
        -- intros Hcon.
           apply H.
           apply AFI_ConsB1_NonRec.
           assumption.
        -- assumption.
      * unfold P_Bindings_NonRec in IHbs.
        apply IHbs with x s.
        -- apply Util.ForallT_tl in X.
           assumption.
        -- intros Hcon.
           apply H.
           apply AFI_ConsB2_NonRec.
           ++ assumption.
           ++ assumption.
        -- assumption.
Qed.

Definition P_Bindings_Rec (bs : list Binding) :=
  Util.ForallT P_Binding bs ->
  forall x,
    ~(appears_free_in_bindings_rec x bs) ->
    forall s bs',
      substitute_bindings_rec x s bs bs' ->
      bs' = bs.

Lemma P_Bindings_Rec__holds_definitionally : forall bs, P_Bindings_Rec bs.
Proof.
  induction bs.
  - unfold P_Bindings_Rec. intros.
    inversion H0. subst.
    reflexivity.
  - unfold P_Bindings_Rec. intros.
    inversion H0.
    subst.
    f_equal.
    + apply Util.ForallT_hd in X.
      unfold P_Binding in X.
      apply X with x s.
      * intros Hcon.
        apply H.
        apply AFI_ConsB1_Rec.
        assumption.
      * assumption.
    + unfold P_Bindings_Rec in IHbs.
      apply IHbs with x s.
      * apply Util.ForallT_tl in X.
        assumption.
      * intros Hcon.
        apply H.
        apply AFI_ConsB2_Rec.
        assumption.
      * assumption.
Qed.

Lemma vacuous_substitution : forall t, P_Term t.
Proof.
  apply Term_rect' with (P := P_Term) (Q := P_Binding).
  - (* Let *)
    intros. unfold P_Term. intros.
    inversion H1; subst.
    + (* S_Let1 *)
      f_equal.
      assert (P_Bindings_NonRec bs) by apply P_Bindings_NonRec__holds_definitionally.
      unfold P_Bindings_NonRec in H2.
      apply H2 with x s.
      * assumption.
      * intros Hcon.
        apply H0.
        apply AFI_LetNonRec.
        assumption.
      * assumption.
    + (* S_Let2 *)
      f_equal.
      * assert (P_Bindings_NonRec bs) by apply P_Bindings_NonRec__holds_definitionally.
        unfold P_Bindings_NonRec in H2.
        apply H2 with x s.
        -- assumption.
        -- intros Hcon.
           apply H0.
           apply AFI_LetNonRec.
           assumption.
        -- assumption.
      * unfold P_Term in H.
        apply H with x s.
        -- intros Hcon.
           apply H0.
           apply AFI_Let.
           ++ assumption.
           ++ assumption.
        -- assumption.
    + (* S_LetRec1 *)
      reflexivity.
    + (* S_LetRec2 *)
      f_equal.
      * assert (P_Bindings_Rec bs) by apply P_Bindings_Rec__holds_definitionally.
        unfold P_Bindings_Rec in H2.
        apply H2 with x s.
        -- assumption.
        -- intros Hcon.
           apply H0.
           apply AFI_LetRec.
           ++ assumption.
           ++ assumption.
        -- assumption.
      * unfold P_Term in H.
        apply H with x s.
        -- intros Hcon.
           apply H0.
           apply AFI_Let.
           ++ assumption.
           ++ assumption.
        -- assumption.
  - (* Var *)
    intros. unfold P_Term. intros.
    inversion H0.
    + (* S_Var1 *)
      subst.
      assert (appears_free_in s (Var s)) by constructor.
      apply H in H1.
      destruct H1.
    + (* S_Var2 *)
      reflexivity.
  - (* TyAbs *)
    intros. unfold P_Term. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s0.
    + intros Hcon.
      apply H0.
      apply AFI_TyAbs.
      assumption.
    + assumption.
  - (* LamAbs *)
    intros. unfold P_Term. intros.
    inversion H1.
    + (* S_LamAbs1 *)
      reflexivity.
    + (* S_LamAbs2 *)
      subst.
      f_equal.
      unfold P_Term in H.
      apply H with x s0.
      * intros Hcon.
        apply H0.
        apply AFI_LamAbs.
        -- assumption.
        -- assumption.
      * assumption.
  - (* Apply *)
    intros. unfold P_Term. intros.
    inversion H2. subst.
    f_equal.
    + unfold P_Term in H. 
      apply H with x s.
      * intros Hcon.
        apply H1.
        apply AFI_Apply1.
        assumption.
      * assumption.
    + unfold P_Term in H0.
      apply H0 with x s.
      * intros Hcon.
        apply H1.
        apply AFI_Apply2.
        assumption.
      * assumption.
  - (* Constant *)
    intros. unfold P_Term. intros.
    inversion H0. subst.
    reflexivity.
  - (* Builtin *)
    intros. unfold P_Term. intros.
    inversion H0. subst.
    reflexivity.
  - (* TyInst *)
    intros. unfold P_Term. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s.
    + intros Hcon.
      apply H0.
      apply AFI_TyInst.
      assumption.
    + assumption.
  - (* Error *)
    intros. unfold P_Term. intros.
    inversion H0. subst.
    reflexivity.
  - (* IWrap *)
    intros. unfold P_Term. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s.
    + intros Hcon.
      apply H0.
      apply AFI_IWrap.
      assumption.
    + assumption.
  - (* Unwrap *)
    intros. unfold P_Term. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s.
    + intros Hcon.
      apply H0.
      apply AFI_Unwrap.
      assumption.
    + assumption.

  - (* TermBind *)
    intros. unfold P_Binding. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s0.
    + intros Hcon.
      apply H0.
      apply AFI_TermBind.
      assumption.
    + assumption.
  - (* TypeBind *)
    intros. unfold P_Binding. intros.
    inversion H0. subst.
    reflexivity.
  - (* DatatypeBind *)
    intros. unfold P_Binding. intros.
    inversion H0. subst.
    reflexivity.
Qed.

Lemma subst_closed : forall t,
    closed t -> 
    forall x s t',
      substitute x s t t' ->
      t' = t.
Proof. Admitted.

Lemma subst_not_afi : forall t x v,
    closed v ->
    forall t',
      substitute x v t t' ->
      ~(appears_free_in x t').
Proof. Admitted.

Lemma duplicate_subst : forall x t v s,
    closed v ->
    forall t' t'',
      substitute x v t t' ->
      substitute x s t' t'' ->
      t'' = t'.
Proof. Admitted.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v ->
    closed v1 ->
    forall t1 t2 t3 t4,
      substitute x v t t1 ->
      substitute x1 v1 t1 t2 ->
      substitute x1 v1 t t3 ->
      substitute x v t3 t4 ->
      t2 = t4.
Proof. Admitted.



(** ** Properties of multi-substitutions *)

Lemma msubst_closed : forall t,
    closed t ->
    forall ss t',
      msubst ss t t' ->
      t' = t.
Proof. Admitted.

Fixpoint closed_env (env : env) :=
  match env with
  | nil => True
  | (x,t) :: env' => closed t /\ closed_env env'
  end.

Lemma subst_msubst : forall env x v t,
    closed v ->
    closed_env env ->
    forall t1 t2 t3 t4,
      substitute x v t t1 ->
      msubst env t1 t2 ->
      msubst (drop x env) t t3 ->
      substitute x v t3 t4 ->
      t2 = t4.
Proof. Admitted.

Lemma msubst_Var : forall ss x,
    closed_env ss ->
    forall t',
      msubst ss (Var x) t' ->
      t' =
        match lookup x ss with
        | Datatypes.Some t => t 
        | None=> Var x
        end.
Proof. 
  induction ss; intros.
  - inversion H0. subst. 
    reflexivity.
  - inversion H0. subst.
    simpl.
    inversion H3; subst.
    + rewrite String.eqb_refl.
      eapply msubst_closed; eauto.
      inversion H; auto.
    + apply String.eqb_neq in H5.
      rewrite H5.
      apply IHss; eauto.
      inversion H; auto.
Qed.

Lemma msubst_Apply : forall ss t1 t2 t',
    msubst ss (Apply t1 t2) t' ->
    exists t1' t2', msubst ss t1 t1' /\ msubst ss t2 t2' /\ t' = (Apply t1' t2').
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists t1, t2.
    eauto using msubst_nil, msubst_cons. 
  - inversion H. subst.
    rename t'0 into t''.
    inversion H2. subst.
    apply IHss in H5.
    destruct H5 as [t1'' [t2'' [H9 [H10 H11]]]].
    exists t1'', t2''.
    split. {
      apply msubst_cons with t1'.
      + assumption.
      + apply H9.
    }
    split. {
      apply msubst_cons with t2'.
      + assumption.
      + apply H10.
    }
    assumption.
Qed.

(** ** Properties of multi-extensions *)

Lemma mupdate_lookup : forall (c : tass) (x : name),
    lookup x c = lookupT (mupdate emptyContext c) x.
Proof. Admitted.

Lemma mupdate_drop : forall (c : tass) Gamma x x',
      lookupT (mupdate Gamma (drop x c)) x' 
    = if String.eqb x x' 
        then lookupT Gamma x' 
        else lookupT (mupdate Gamma c) x'.
Proof. Admitted.



(** ** Properties of Instantiations *)

Lemma instantiation_domains_match : forall c e1 e2,
    instantiation c e1 e2 ->
    forall x T,
      lookup x c = Datatypes.Some T ->
      exists t1 t2,
        lookup x e1 = Datatypes.Some t1 /\
        lookup x e2 = Datatypes.Some t2.
Proof.
  intros c e1 e2 V. 
  induction V; intros x0 T0 C.
  - discriminate.
  - simpl.
    simpl in C.
    destruct (x =? x0) eqn:Heqb.
    + eauto.
    + apply IHV with T0.
      assumption.
Qed.

Lemma instantiation_env_closed : forall c e1 e2,
    instantiation c e1 e2 ->
    closed_env e1 /\ closed_env e2.
Proof.
  intros c e1 e2 V.
  induction V; intros.
  - split; reflexivity.
  - split.
    + simpl.
      split.
      * apply typable_empty__closed with T.
        apply R_typable_empty_1 with v2.
        assumption.
      * apply IHV.
    + simpl.
      split.
      * apply typable_empty__closed with T.
        apply R_typable_empty_2 with v1.
        assumption.
      * apply IHV.
Qed.
    

Corollary instantiation_env_closed_1 : forall c e1 e2,
    instantiation c e1 e2 ->
    closed_env e1.
Proof. intros. destruct (instantiation_env_closed _ _ _ H). assumption. Qed.

Corollary instantiation_env_closed_2 : forall c e1 e2,
    instantiation c e1 e2 ->
    closed_env e2.
Proof. intros. destruct (instantiation_env_closed _ _ _ H). assumption. Qed.

Lemma instantiation_R : forall c e1 e2,
    instantiation c e1 e2 ->
    forall x T v1 v2,
      lookup x c = Datatypes.Some T ->
      lookup x e1 = Datatypes.Some v1 ->
      lookup x e2 = Datatypes.Some v2 ->
      R T v1 v2.
Proof.
  intros c e1 e2 V.
  induction V; intros x' T' v1' v2' G E1 E2.
  - destruct x'; discriminate.
  - inversion G. subst.
    inversion E1. subst.
    inversion E2. subst.
    destruct (x =? x').
    + inversion H3. subst.
      inversion H4. subst.
      inversion H5. subst.
      assumption. 
    + apply IHV with x'; assumption.
Qed.

Lemma instantiation_drop : forall c e1 e2,
    instantiation c e1 e2 ->
    forall x,
      instantiation (drop x c) (drop x e1) (drop x e2).
Proof.
  intros c e1 e2 V.
  induction V.
  - intros. simpl. apply V_nil.
  - intros. simpl.
    destruct (x =? x0).
    + apply IHV.
    + apply V_cons.
      * assumption.
      * assumption.
      * assumption.
      * apply IHV.
Qed.

(** ** Congruence lemmas on [eval] *)

(** ** Multi-substitutions preserve typing *)

Lemma msubst_preserves_typing_1 : forall c e1 e2,
    instantiation c e1 e2 ->
    forall Gamma t t' S,
      (mupdate Gamma c) |-+ t : S ->
      msubst e1 t t' ->
      Gamma |-+ t': S. 
Proof.
  intros c e1 e2 V.
  induction V.
  - intros.
    simpl in H.
    inversion H0. subst.
    assumption.
  - intros.
    simpl in H2.
    inversion H3. subst.
    apply IHV with t'0.
    + eapply substitution_preserves_typing.
      * apply H2.
      * apply R_typable_empty_1 with v2.
        apply H1.
      * apply H9.
    + apply H10.
Qed. 

Lemma msubst_preserves_typing_2 : forall c e1 e2,
    instantiation c e1 e2 ->
    forall Gamma t t' S,
      (mupdate Gamma c) |-+ t : S ->
      msubst e2 t t' ->
      Gamma |-+ t': S. 
Proof.
  intros c e1 e2 V.
  induction V.
  - intros.
    simpl in H.
    inversion H0. subst.
    assumption.
  - intros.
    simpl in H2.
    inversion H3. subst.
    apply IHV with t'0.
    + eapply substitution_preserves_typing.
      * apply H2.
      * apply R_typable_empty_2 with v1.
        apply H1.
      * apply H9.
    + apply H10.
Qed. 

(** ** The [R] Lemma *)

Definition P_has_type ctx t1 T := 
  forall c e1 e2 t2,
    ctx = mupdate emptyContext c ->
    ctx |-+ t1 : T ->
    ctx |-+ t2 : T ->
    instantiation c e1 e2 ->
    CNR_Term t1 t2 ->
    forall t1' t2',
      msubst e1 t1 t1' ->
      msubst e2 t2 t2' ->
      R T t1' t2'.

Definition P_constructor_well_formed ctx c := ctx |-ok_c c.

Definition P_bindings_well_formed_nonrec ctx bs1 := ctx |-oks_nr bs1.

Definition P_bindings_well_formed_rec ctx bs1 := ctx |-oks_r bs1.

Definition P_binding_well_formed ctx b1 := ctx |-ok b1.

Axiom skip : forall P, P.

 (*forall c e1 e2 t1 t2 T,
    (mupdate emptyContext c) |-+ t1 : T ->
    (mupdate emptyContext c) |-+ t2 : T ->
    instantiation c e1 e2 ->
    CNR_Term t1 t2 ->
    forall t1' t2',
      msubst e1 t1 t1' ->
      msubst e2 t2 t2' ->
      R T t1' t2'.*)

Lemma msubst_R : forall ctx t1 T,
    ctx |-+ t1 : T ->
    P_has_type ctx t1 T.
Proof.
  apply has_type__ind with 
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).
  - intros. unfold P_has_type. intros. subst.
    apply skip.
  - intros. unfold P_has_type. intros. subst.
    apply skip.

  - (* T_Var *)
    intros. 
    unfold P_has_type. 
    intros c e1 e2 t2 Heq Ht1 Ht2 V Hds t1' t2' X1 X2.
    subst.

    inversion Hds. subst.
    inversion X. subst.

    assert (forall x, lookupT (mupdate emptyContext c) x = lookup x c). {
      intros. rewrite mupdate_lookup. auto.
    }
    rewrite H0 in H.
    destruct (instantiation_domains_match _ _ _ V _ _ H) as [t1'' [t2'' [Ht1'' Ht2'']]].
    destruct (instantiation_env_closed _ _ _ V) as [He1 He2].
    apply instantiation_R with c e1 e2 x.
    + assumption.
    + assumption.
    + rewrite msubst_Var with e1 x t1'.
      * rewrite Ht1''.
        reflexivity.
      * assumption.
      * assumption.
    + rewrite msubst_Var with e2 x t2'.
      * rewrite Ht2''.
        reflexivity.
      * assumption.
      * assumption.

  - (* T_Forall *)
    apply skip.

  - (* T_LamAbs *)
    apply skip.

  - (* T_Apply *)
    intros ctx t1_1 t1_2 T1 T2 Ht1_1 IH1_1 Ht1_2 IH1_2.
    unfold P_has_type.
    intros c e1 e2 t2 Heq Ht1 Ht2 V Hds t1' t2' Hms1 Hms2.
    subst.

    inversion Hds. subst.
    inversion X. subst.
    rename s' into t2_1.
    rename t' into t2_2.
    destruct (msubst_Apply _ _ _ _ Hms1) as [t1_1' [t1_2' [Hms_t1_1' [Hms_t1_2' Heq1']]]].
    destruct (msubst_Apply _ _ _ _ Hms2) as [t2_1' [t2_2' [Hms_t2_1' [Hms_t2_2' Heq2']]]].
    subst.

    assert (emptyContext |-+ (Apply t1_1' t1_2') : T2) by eauto using msubst_preserves_typing_1.
    assert (emptyContext |-+ (Apply t2_1' t2_2') : T2) by eauto using msubst_preserves_typing_2.

    destruct (progress _ _ H) as [v1 Hv1].
    destruct (progress _ _ H0) as [v2 Hv2].

    assert (R (Ty_Fun T1 T2) t1_1' t2_1'). {
      unfold P_has_type in IH1_1.
      apply IH1_1 with c e1 e2 t2_1.
      - reflexivity.
      - assumption.
      - eapply CNR_Term__preserves_typing; eauto.
      - apply V.
      - assumption.
      - assumption.
      - assumption.
    }

    assert (R T1 t1_2' t2_2'). {
      unfold P_has_type in IH1_2.
      apply IH1_2 with c e1 e2 t2_2. 
      - reflexivity.
      - assumption.
      - eapply CNR_Term__preserves_typing; eauto.
      - apply V.
      - assumption.
      - assumption.
      - assumption.
    }

    destruct T2.
    + (* Ty_Var *) 
      apply R_functional_extensionality in H1.
      destruct H1 as [v1' [v2' [Hv1' [Hv2' Hfe]]]].
      apply Hfe in H2.
      apply R_falsity in H2.
      destruct H2.
    + (* Ty_Fun *)
      split; auto.
      split; auto.
      exists v1.
      exists v2.
      split; auto.
      split; auto.

      destruct (R_functional_extensionality _ _ _ _ H1) as [v1_1' [v2_1' [Hv1_1' [Hv2_1' Hfe']]]].
      apply Hfe' in H2.

      destruct (R_functional_extensionality _ _ _ _ H2) as [v1' [v2' [Hv1' [Hv2' Hfe]]]].

      assert (Apply v1_1' t1_2' ==> v1). {
        eapply eval_congr_Apply1.
        - apply Hv1.
        - assumption.
      }
      assert (Apply v2_1' t2_2' ==> v2). {
        eapply eval_congr_Apply1.
        - apply Hv2.
        - assumption.
      }

      assert (v1 = v1') by (eapply eval__deterministic; eauto).
      assert (v2 = v2') by (eapply eval__deterministic; eauto).
      subst.
      apply Hfe.
    + (* Ty_IFix *)
      split; auto.
      split; auto.
      eexists.
      eexists.
      eauto.
    + (* Ty_Forall *)
      split; auto.
      split; auto.
      eexists.
      eexists.
      eauto.
    + (* Ty_Builtin *)
      split; auto.
      split; auto.
      exists v1.
      exists v2.
      split; auto.
      split; auto.

      destruct (R_functional_extensionality _ _ _ _ H1) as [v1_1' [v2_1' [Hv1_1' [Hv2_1' Hfe']]]].
      apply Hfe' in H2.

      destruct (R_syntactic_equality _ _ _ H2) as [v1' [v2' [Hv1' [Hv2' Heq]]]].
      subst.

      assert (Apply v1_1' t1_2' ==> v1). {
        eapply eval_congr_Apply1.
        - apply Hv1.
        - assumption.
      }
      assert (Apply v2_1' t2_2' ==> v2). {
        eapply eval_congr_Apply1.
        - apply Hv2.
        - assumption.
      }

      assert (v1 = v2') by (eapply eval__deterministic; eauto).
      assert (v2 = v2') by (eapply eval__deterministic; eauto).

      subst.

      reflexivity.

    + (* Ty_Lam *)
      apply R_functional_extensionality in H1.
      destruct H1 as [v1' [v2' [Hv1' [Hv2' Hfe]]]].
      apply Hfe in H2.
      apply R_falsity in H2.
      destruct H2.
    + (* Ty_App *) 
      apply R_functional_extensionality in H1.
      destruct H1 as [v1' [v2' [Hv1' [Hv2' Hfe]]]].
      apply Hfe in H2.
      apply R_falsity in H2.
      destruct H2.

  - 

Proof. Abort.
