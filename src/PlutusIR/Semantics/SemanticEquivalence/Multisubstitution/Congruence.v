Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Util.
Require Import PlutusCert.Util.List.
Require Import PlutusCert.Util.Map.
Require Import PlutusCert.Util.Map.Mupdate.

Import PlutusNotations.

Require Import Arith.
Require Import Coq.Lists.List.

Local Open Scope string_scope.
Local Open Scope list_scope.



Lemma In__mdrop : forall {X} ns ss x s,
    List.In x ns ->
    @mdrop X ns ((x, s) :: ss) = @mdrop X ns ss.
Proof.
  induction ns; intros.
  - destruct H.
  - simpl.
    destruct (x =? a)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      destruct H.
      * symmetry in H.
        apply Hneq in H.
        destruct H.
      * eapply IHns.
        assumption.
Qed.


Lemma drop_comm : forall {X} x y (xs : list (string * X)) ,
  drop x (drop y xs) = drop y (drop x xs).
Proof with auto.
  intros.
  induction xs...
  simpl.
  destruct a as [z v].
  destruct (z =? y) eqn:Heqb;
  destruct (z =? x) eqn:Heqb'...

  - simpl. rewrite Heqb...
  - simpl. rewrite Heqb'...
  - simpl. rewrite Heqb, Heqb'.
    congruence...
Qed.

Lemma drop_mdrop : forall X n ns (xs : list (string * X)),
  drop n (mdrop ns xs) = mdrop ns (drop n xs).
Proof. induction ns.
  - auto.
  - intros.
    simpl.
    rewrite IHns.
    rewrite drop_comm.
    reflexivity.
Qed.



Lemma In__mdrop_drop : forall {X} ns ss x,
    List.In x ns ->
    @mdrop X ns (drop x ss) = @mdrop X ns ss.
Proof.
  intros.
  revert ss.
  induction ns.
  all: intros ss.
  - inversion H.
  - simpl.
    destruct H; subst.
    + rewrite drop_idempotent.
      congruence.
    + rewrite drop_comm.
      auto.
Qed.

Lemma not_In__mdrop : forall {X} ns ss x s,
    ~ List.In x ns ->
    @mdrop X ns ((x, s) :: ss) = (x, s) :: @mdrop X ns ss.
Proof.
  induction ns; intros.
  - reflexivity.
  - simpl.
    destruct (x =? a)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      exfalso.
      apply H.
      left.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      eapply IHns.
      intros Hcon.
      apply H.
      right.
      assumption.
Qed.

Lemma subst_b__bound_vars : forall x s b,
    bvb b = bvb <{ [s/x][b] b }>.
Proof. intros. induction b. all: eauto. destruct v. eauto. Qed.

Lemma subst_bnr__bound_vars : forall x s bs,
    bvbs bs = bvbs <{ [s/x][bnr] bs }>.
Proof.
  intros.
  induction bs.
  - reflexivity.
  - simpl.
    destruct (List.existsb (eqb x) (bvb a)) eqn:Hexb.
    + unfold bvbs.
      simpl.
      f_equal.
      apply subst_b__bound_vars.
    + unfold bvbs.
      simpl.
      f_equal.
      * apply subst_b__bound_vars.
      * assumption.
Qed.

Lemma msubst_bnr__bound_vars : forall bs ss,
    bvbs bs = bvbs <{ /[ ss /][bnr] bs }>.
Proof with eauto.
  intros bs ss.
  generalize bs.
  induction ss...
  clear bs.
  intros.
  destruct a.
  simpl.
  rewrite <- IHss.
  apply subst_bnr__bound_vars.
Qed.

Lemma substA_b__bound_tyvars : forall a T b,
    btvb b = btvb <{ [[T/a][b] b }>.
Proof. intros. induction b. all: eauto. destruct v; eauto. destruct d; eauto. Qed.

Lemma substA_bnr__bound_tyvars : forall a T bs,
    btvbs bs = btvbs <{ [[T/a][bnr] bs }>.
Proof.
  intros.
  induction bs.
  - reflexivity.
  - simpl.
    destruct (List.existsb (eqb a) (btvb a0)) eqn:Hfind.
    + unfold btvbs.
      simpl.
      f_equal.
      apply substA_b__bound_tyvars.
    + unfold btvbs.
      simpl.
      f_equal.
      * apply substA_b__bound_tyvars.
      * assumption.
Qed.

Lemma substA_c__bvc : forall c a T,
  bvc <{ [[T / a][c] c }> = bvc c.
Admitted.

Lemma substA_cs__bvc : forall cs a T,
  map bvc <{ [[T / a][cs] cs }> = map bvc cs.
Admitted.

Lemma substA_b__bvb : forall a T b,
    bvb b = bvb <{ [[T/a][b] b }>.
Proof with eauto.
  destruct b; simpl.
  - destruct v...
  - destruct t...
  - destruct d, t.
    simpl.
    rewrite substA_cs__bvc...
Qed.

Lemma substA_bnr__bvbs : forall a T bs,
    bvbs bs = bvbs <{ [[T/a ][bnr] bs }>.
Proof with eauto.
  induction bs...
  simpl.
  destruct (existsb (eqb a) (btvb a0)); simpl.
  - setoid_rewrite bvbs_cons.
    rewrite <- substA_b__bvb...
  - setoid_rewrite bvbs_cons.
    rewrite <- IHbs.
    rewrite <- substA_b__bvb...
Qed.

Lemma msubstA_bnr__bvbs : forall ss bs,
    bvbs bs = bvbs <{ /[[ ss /][bnr] bs }>.
Proof with eauto.
  induction ss...
  destruct a.
  simpl.
  intros.
  setoid_rewrite <- IHss.
  rewrite <- substA_bnr__bvbs...
Qed.

Lemma msubst_LetNonRec_nil : forall ss e,
    msubst ss (Let NonRec nil e) = Let NonRec nil (msubst ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_LetNonRec : forall ss bs e,
    msubst ss (Let NonRec bs e) = Let NonRec (msubst_bnr ss bs) (msubst (mdrop (bvbs bs) ss) e).
Proof with auto.
  induction ss; intros.
  - rewrite mdrop_nil. reflexivity.
  - destruct a. simpl.
    destruct (existsb (eqb s) (bvbs bs)) eqn:Hexb.
    + apply existsb_exists in Hexb.
      destruct Hexb as [x [HIn Heqb]].
      apply eqb_eq in Heqb as Heq.
      subst.
      rewrite In__mdrop...
      erewrite subst_bnr__bound_vars.
      eapply IHss.
    + rewrite not_In__mdrop...
      * simpl.
        erewrite subst_bnr__bound_vars.
        eapply IHss.
      * intros Hcon.
        eapply existsb_nexists.
        -- eapply Hexb.
        -- exists s.
           rewrite eqb_refl.
           auto.
Qed.

Lemma msubst_TermBind : forall ss stricty x T e,
    msubst_b ss (TermBind stricty (VarDecl x T) e) = TermBind stricty (VarDecl x T) (msubst ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_bnr_cons : forall ss b bs,
    msubst_bnr ss (b :: bs) = msubst_b ss b :: msubst_bnr (mdrop (bvb b) ss) bs.
Proof.
  induction ss; intros.
  - rewrite mdrop_nil. reflexivity.
  - destruct a.
    simpl.
    destruct (existsb (eqb s) (bvb b)) eqn:Hexb.
    + apply existsb_exists in Hexb.
      destruct Hexb as [x [HIn Heqb]].
      apply eqb_eq in Heqb as Heq.
      subst.
      rewrite In__mdrop.
      * erewrite subst_b__bound_vars.
        eapply IHss.
      * assumption.
    + apply existsb_nexists in Hexb.
      rewrite not_In__mdrop.
      * simpl.
        erewrite subst_b__bound_vars.
        eapply IHss.
      * intros Hcon.
        apply Hexb.
        exists s.
        rewrite eqb_refl.
        auto.
Qed.

Lemma msubstA_LetNonRec_nil : forall ss e,
    msubstA ss (Let NonRec nil e) = Let NonRec nil (msubstA ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_LetNonRec : forall ss bs e,
    msubstA ss (Let NonRec bs e) = Let NonRec (msubstA_bnr ss bs) (msubstA (mdrop (btvbs bs) ss) e).
Proof.
(* ADMIT: I had no time to finish this. Should hold, it is a congruence lemma. *)
Admitted.

Lemma msubstA_LetRec : forall ss bs e,
    msubstA ss (Let Rec bs e) = Let Rec (msubstA_br (mdrop (btvbs bs) ss) bs) (msubstA (mdrop (btvbs bs) ss) e).
Proof.
(* ADMIT: I had no time to finish this. Should hold, it is a congruence lemma. *)
Admitted.

Lemma msubstA_TermBind : forall ss stricty x T e,
    msubstA_b ss (TermBind stricty (VarDecl x T) e) = TermBind stricty (VarDecl x (msubstT ss T)) (msubstA ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_BindingsNonRec_cons : forall ss b bs,
    msubstA_bnr ss (b :: bs) = msubstA_b ss b :: msubstA_bnr (mdrop (btvb b) ss) bs.
Proof.
(* ADMIT: I had no time to finish this. Should hold, it is a congruence lemma. *)
Admitted.

Lemma msubst__fold : forall ss x v t,
    msubst ss <{ [v / x] t }> = msubst ((x, v) :: ss) t.
Proof. induction ss; intros; auto. Qed.

Lemma msubst_bnr__fold : forall ss x v bs,
    msubst_bnr ss <{ [v / x][bnr] bs }> = msubst_bnr ((x, v) :: ss) bs.
Proof. induction ss; intros; auto. Qed.

Lemma msubst_LamAbs : forall ss x T t0,
    msubst ss (LamAbs x T t0) = LamAbs x T (msubst (drop x ss) t0).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a.
    simpl.
    destruct (s =? x)%string eqn:Heqb.
    + eauto using eqb_eq.
    + eauto using eqb_neq.
Qed.

Lemma msubstA_LamAbs : forall ss x T t0,
    msubstA ss (LamAbs x T t0) = LamAbs x (msubstT ss T) (msubstA ss t0).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstT_TyFun : forall ss T1 T2,
    msubstT ss (Ty_Fun T1 T2) = Ty_Fun (msubstT ss T1) (msubstT ss T2).
Proof.
  induction ss.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_Apply : forall ss t1 t2,
    msubst ss (Apply t1 t2) = Apply (msubst ss t1) (msubst ss t2).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_Apply : forall ss t1 t2,
    msubstA ss (Apply t1 t2) = Apply (msubstA ss t1) (msubstA ss t2).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_Builtin : forall ss f,
    msubst ss (Builtin f) = Builtin f.
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_Builtin : forall ss f,
    msubstA ss (Builtin f) = Builtin f.
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_Constant : forall ss sv,
    msubst ss (Constant sv) = Constant sv.
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a.
    eauto.
Qed.

Lemma msubstA_Constant : forall ss sv ,
    msubstA ss (Constant sv) = Constant sv.
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstT_TyBuiltin : forall ss T,
    msubstT ss (Ty_Builtin T) = Ty_Builtin T.
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_DatatypeBind : forall ss X YKs matchFunc cs,
    msubst_b ss (DatatypeBind (Datatype X YKs matchFunc cs)) = DatatypeBind (Datatype X YKs matchFunc cs).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_DatatypeBind : forall ss X YKs matchFunc cs,
    msubstA_b ss (DatatypeBind (Datatype X YKs matchFunc cs)) = DatatypeBind (Datatype X YKs matchFunc (msubstA_cs ss cs)).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. simpl. eauto.
Qed.


Lemma msubst_Error : forall ss T,
    msubst ss (Error T) = Error T.
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_Error : forall ss T,
    msubstA ss (Error T) = Error (msubstT ss T).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_IWrap : forall ss F T M,
    msubst ss (IWrap F T M) = IWrap F T (msubst ss M).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_IWrap : forall ss F T M,
    msubstA ss (IWrap F T M) = IWrap (msubstT ss F) (msubstT ss T) (msubstA ss M).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstT_IFix : forall ss F T,
    msubstT ss (Ty_IFix F T) = Ty_IFix (msubstT ss F) (msubstT ss T).
Proof.
  induction ss; intros.
    - reflexivity.
    - destruct a. eauto.
Qed.

Lemma msubst_TyAbs : forall ss bX K t0,
    msubst ss (TyAbs bX K t0) = TyAbs bX K (msubst ss t0).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.

Lemma msubstA_TyAbs : forall ss bX K t0,
    msubstA ss (TyAbs bX K t0) = TyAbs bX K (msubstA (drop bX ss) t0).
Proof. induction ss; intros. - reflexivity. - intros. destruct a. simpl. destruct (s =? bX)%string; eauto. Qed.


Lemma msubstT_TyForall : forall ss bX K T,
    msubstT ss (Ty_Forall bX K T) = Ty_Forall bX K (msubstT (drop bX ss) T).
Proof. induction ss; intros. - reflexivity. - intros. destruct a. simpl. destruct (s =? bX)%string; eauto. Qed.

Lemma msubst_TyInst : forall ss t0 T0,
    msubst ss (TyInst t0 T0) = TyInst (msubst ss t0) T0.
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.


Lemma msubstA_TyInst : forall ss t0 T0,
    msubstA ss (TyInst t0 T0) = TyInst (msubstA ss t0) (msubstT ss T0).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.


Lemma msubst_Unwrap : forall ss M,
    msubst ss (Unwrap M) = Unwrap (msubst ss M).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.

Lemma msubstA_Unwrap : forall ss M ,
    msubstA ss (Unwrap M) = Unwrap (msubstA ss M).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.

Lemma msubstA_Constr : forall ss n ts ,
    msubstA ss (Constr n ts) = Constr n (map (msubstA ss) ts).
Proof. induction ss; intros.
  - simpl. rewrite map_id. reflexivity.
  - destruct a. simpl. rewrite IHss. rewrite map_map. reflexivity.
Qed.

Lemma msubstA_Case : forall ss t ts,
    msubstA ss (Case t ts) = Case (msubstA ss t) (map (msubstA ss) ts).
Proof.
  induction ss; intros. 
  - simpl. rewrite map_id. reflexivity.
  - destruct a. 
    simpl.
    rewrite IHss.
    rewrite map_map.
    reflexivity.
Qed.

Lemma msubst_Var : forall ss x,
    closed_env ss ->
    msubst ss (Var x) =
      match lookup x ss with
      | Some t => t
      | None => Var x
      end.
Proof.
  induction ss; intros.
  - reflexivity.
  - intros.
    destruct a.
    simpl.
    destruct (s =? x)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      destruct H.
      rewrite msubst_closed.
      all: auto.
    + apply eqb_neq in Heqb as Hneq.
      destruct H.
      eapply IHss.
      assumption.
Qed.

Lemma msubstA_Var : forall ss x,
    msubstA ss (Var x) = Var x.
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.


(* TODO move this into separate module*)

Hint Rewrite
  msubstA_LetRec
  msubstA_LetNonRec
  msubstA_bnr__bvbs
  msubstA_LetNonRec_nil
  msubstA_LetNonRec
  msubstA_LetRec
  msubstA_TermBind
  msubstA_BindingsNonRec_cons
  msubstA_LamAbs
  msubstA_Apply
  msubstA_Builtin
  msubstA_Constant
  msubstA_DatatypeBind
  msubstA_Error
  msubstA_IWrap
  msubstA_TyAbs
  msubstA_TyInst
  msubstA_Unwrap
  msubstA_Var
  msubstA_Constr
  msubstA_Case
  : msubstA_cong.

Lemma not_is_error_msubstA : forall v ss, ~ is_error v -> ~ is_error (msubstA ss v).
  intros v ss H_not_err H_err.
  destruct v; simpl in H_err.
  all: try (autorewrite with msubstA_cong in H_err; inversion H_err).

  (* Let r bs t *)
  - destruct r.
    + autorewrite with msubstA_cong in H_err.
       inversion H_err.
    + rewrite msubstA_LetRec in H_err.
       inversion H_err.

  (* Error *)
  - apply H_not_err.
    constructor.
Qed.

