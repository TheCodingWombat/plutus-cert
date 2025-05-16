Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Util.List.

Import PlutusNotations.

Require Import Coq.Lists.List.
Import ListNotations.



(** * Helper lemmas *)

Lemma subst_b__preserves_bindsD : forall b v x,
    binds_Delta <{ [x := v]b b }> = binds_Delta b.
Proof with eauto.
  intros.
  destruct b.
  all: simpl.
  - destruct v0...
  - destruct t...
  - destruct d...
Qed.

Lemma subst_b__preserves_bindsG : forall b v x,
    binds_Gamma <{ [x := v]b b }> = binds_Gamma b.
Proof with eauto.
  intros.
  destruct b.
  all: simpl.
  - destruct v0...
  - destruct t...
  - destruct d...
Qed.

Lemma subst_bnr__preserves_bindsD : forall bs v x,
    map binds_Delta <{ [x := v]bnr bs }> = map binds_Delta bs.
Proof with eauto.
  induction bs; intros...
  - simpl.
    destruct (existsb (eqb x) (bvb a)).
    all: simpl.
    all: f_equal.
    all: eauto using subst_b__preserves_bindsD.
Qed.

Lemma subst_bnr__preserves_bindsG : forall bs v x,
    map binds_Gamma <{ [x := v]bnr bs }> = map binds_Gamma bs.
Proof with eauto.
  induction bs; intros...
  - simpl.
    destruct (existsb (eqb x) (bvb a)).
    all: simpl.
    all: f_equal.
    all: eauto using subst_b__preserves_bindsG.
Qed.

Lemma subst_br__preserves_bindsD : forall bs v x,
    map binds_Delta <{ [x := v]br bs }> = map binds_Delta bs.
Proof with eauto.
  induction bs; intros...
  - simpl.
    f_equal.
    all: eauto using subst_b__preserves_bindsD.
Qed.

Lemma subst_br__preserves_bindsG : forall bs v x,
    map binds_Gamma <{ [x := v]br bs }> = map binds_Gamma bs.
Proof with eauto.
  induction bs; intros...
  - simpl.
    f_equal.
    all: eauto using subst_b__preserves_bindsG.
Qed.


Lemma NoDup__btvbs bs x v :
  NoDup (btvbs bs) ->
  NoDup (btvbs (subst_br x v bs)).
Admitted.

Lemma NoDup__bvbs bs x v :
  NoDup (bvbs bs) ->
  NoDup (bvbs (subst_br x v bs)).
Admitted.
(** * Propositions *)

Definition P_Term (t : term) :=
  forall Delta Gamma x U Un v T,
    Delta ,, ((x, U) :: Gamma) |-+ t : T ->
    normalise U Un ->
    [] ,, [] |-+ v : Un ->
    Delta ,, Gamma |-+ <{ [x := v] t }> : T.

Definition P_Binding (b : binding) : Prop :=
  forall Delta Gamma rec x U Un v,
    Delta ,, ((x, U) :: Gamma) |-ok_b rec # b ->
    normalise U Un ->
    [] ,, [] |-+ v : Un ->
    Delta ,, Gamma |-ok_b rec # <{ [x := v]b b }>.

#[export] Hint Unfold
  P_Term
  P_Binding
  : core.



(** * Binding sequences *)

Lemma SPT__Bindings_NonRec : forall bs,
    Util.ForallP P_Binding bs ->
    forall Delta Gamma x U Un v,
      Delta ,, ((x, U) :: Gamma) |-oks_nr bs ->
      normalise U Un ->
      [] ,, [] |-+ v : Un ->
      Delta ,, Gamma |-oks_nr <{ [x := v]bnr bs }>.
Proof with (eauto with typing).
  induction bs. all: intros...
  - simpl.
    inversion H0. subst.
    destruct (existsb (eqb x) (bvb a)) eqn:Hexb.
    + eapply W_ConsB_NonRec...
      * eapply Util.ForallP_hd in H.
        eapply H...
      * rewrite subst_b__preserves_bindsG...
      * rewrite subst_b__preserves_bindsD...
        eapply existsb_exists in Hexb.
        destruct Hexb as [x0 [HIn Heqb]].
        apply eqb_eq in Heqb as Heq.
        subst.
        apply In_bvb_bindsG in HIn.
        eapply In__map_normalise in H8...
        eapply Typing.weakening in H9.
        unfold Typing.P_bindings_well_formed_nonrec in H9.
        apply H9...
        all: auto using inclusion_refl, append_shadow.
    + eapply W_ConsB_NonRec...
      * eapply Util.ForallP_hd in H.
        eapply H...
      * rewrite subst_b__preserves_bindsG...
      * rewrite subst_b__preserves_bindsD...
        eapply IHbs...
        -- eapply Util.ForallP_tl...
        -- eapply Util.existsb_nexists in Hexb.
           assert (~ In x (bvb a)). {
             intros Hcon.
             apply Hexb.
             exists x.
             split...
             apply eqb_refl.
           }
           apply notIn_bvb_bindsG in H3.
           eapply notIn__map_normalise in H8...
           apply Typing.weakening in H9.
           apply H9.
           all: auto using inclusion_refl, append_permute.
Qed.

Lemma SPT__Bindings_Rec : forall bs,
    Util.ForallP P_Binding bs ->
    forall Delta Gamma x U Un v,
      Delta ,, ((x, U) :: Gamma) |-oks_r bs ->
      normalise U Un ->
      [] ,, [] |-+ v : Un ->
      Delta ,, Gamma |-oks_r <{ [x := v]br bs }>.
Proof with (eauto with typing).
  induction bs. all: intros...
  - simpl.
    inversion H0. subst.
    eapply W_ConsB_Rec...
    + eapply Util.ForallP_hd in H...
    + eapply Util.ForallP_tl in H...
Qed.

Lemma subst_bnr'__preserves__btvbs x v bs :
  btvbs (@subst_bnr' subst_b x v bs) = btvbs bs.
Proof.
  apply binds_Delta__btvbs.
  rewrite subst_bnr__preserves_bindsD.
  reflexivity.
Qed.

Lemma subst_br'__preserves__btvbs x v bs :
  btvbs (@subst_br' subst_b x v bs) = btvbs bs.
Proof.
  apply binds_Delta__btvbs.
  rewrite subst_br__preserves_bindsD.
  reflexivity.
Qed.

(** * Main lemmas *)

Lemma substitution_preserves_typing :
  (forall t, P_Term t) /\ (forall b, P_Binding b).
Proof with eauto.
  apply term__multind with
    (P := P_Term)
    (Q := P_Binding).
  all: intros; autounfold; intros.
  all: try solve [try (inversion H || inversion H0 || inversion H1); subst; eauto with typing].
  - inversion H1. all: subst.
    + simpl.
      destruct (existsb (eqb x) (bvbs bs)) eqn:Hexb.
      * eapply T_Let...
        -- rewrite subst_bnr__preserves_bindsG...
        -- eapply SPT__Bindings_NonRec...
        -- rewrite subst_bnr__preserves_bindsD...
            eapply existsb_exists in Hexb.
            destruct Hexb as [x0 [HIn Heqb]].
            apply eqb_eq in Heqb as Heq.
            subst.
            apply In_bvbs_bindsG in HIn.
            eapply In__map_normalise in HIn...
            apply Typing.weakening in H13.
            apply H13.
            all: auto using inclusion_refl, append_shadow.
        -- simpl. 
           erewrite btvbs_eq__drop_Δ_eq; eauto.
           rewrite subst_bnr'__preserves__btvbs; eauto.
            
      * eapply T_Let...
        -- rewrite subst_bnr__preserves_bindsG...
        -- eapply SPT__Bindings_NonRec...
        -- rewrite subst_bnr__preserves_bindsD...
           eapply H0...
            eapply Util.existsb_nexists in Hexb.
            assert (~ In x (bvbs bs)). {
              intros Hcon.
              apply Hexb.
              exists x.
              split...
              apply eqb_refl.
            }
            apply notIn_bvbs_bindsG in H4.
            eapply notIn__map_normalise in H4...
            apply Typing.weakening in H13.
            apply H13.
            all: auto using inclusion_refl, append_permute.
        -- erewrite btvbs_eq__drop_Δ_eq; eauto.
           rewrite subst_bnr'__preserves__btvbs; eauto.
    + simpl.
      destruct (existsb (eqb x) (bvbs bs)) eqn:Hexb.
      * eapply existsb_exists in Hexb.
        destruct Hexb as [x0 [HIn Heqb]].
        apply eqb_eq in Heqb as Heq.
        subst.
        apply In_bvbs_bindsG in HIn.
        eapply In__map_normalise in HIn...
        eapply T_LetRec...
        -- apply Typing.weakening in H12.
           apply H12.
           all: auto using inclusion_refl, append_shadow.
        -- apply Typing.weakening in H15.
           apply H15.
           all: auto using inclusion_refl, append_shadow.
      * eapply Util.existsb_nexists in Hexb.
        assert (~ In x (bvbs bs)). {
          intros Hcon.
          apply Hexb.
          exists x.
          split...
          rewrite eqb_refl...
        }
        apply notIn_bvbs_bindsG in H4...
        eapply notIn__map_normalise in H4...
        eapply T_LetRec...
        -- eauto using NoDup__btvbs.
        -- eauto using NoDup__bvbs.
        -- rewrite subst_br__preserves_bindsG...
        -- rewrite subst_br__preserves_bindsD...
           eapply SPT__Bindings_Rec...
           apply Typing.weakening in H12.
           apply H12.
           all: auto using inclusion_refl, append_permute.
        -- rewrite subst_br__preserves_bindsD...
           eapply H0.
           ++
              apply Typing.weakening in H15.
              apply H15.
              all: auto using inclusion_refl, append_permute.
           ++ apply H2.
           ++ assumption.
        -- erewrite btvbs_eq__drop_Δ_eq; eauto.
           rewrite subst_br'__preserves__btvbs; eauto.
  - (* Var *)
    simpl.
    destruct (x =? s)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      inversion H.
      subst.
      simpl in H3.
      rewrite Heqb in H3.
      assert (U = T0) by congruence. subst.
      inversion H3. subst.
      assert (Un = T) by eauto using normalisation__deterministic.
      subst.
      eapply Typing.weakening_empty; eauto.
    + apply eqb_neq in Heqb as Hneq.
      inversion H. subst.
      eapply T_Var...
      simpl in H3.
      rewrite Heqb in H3...
  - (* TyAbs *)
    simpl.
    inversion H0; subst.
    apply T_TyAbs; auto.
    unfold P_Term in H.
    eapply H; eauto.
    (* Suppose s not in U, then done by unfold.
       Suppose s free in U.
       then x not in (drop_ty_var s ((x, U) :: Gamma)).
       then x not free in t.
       then we can strengthen the goal and remove (x, U).
       Then drop_ty_var of smaller context is included in
       drop_ty_var of superset of that context.
      *)
    admit.
  - (* LamAbs *)
    inversion H0. subst.
    simpl.
    destruct (x =? s)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      apply T_LamAbs...
      apply Typing.weakening_term with (Delta' := Delta) (Gamma' := ((s, T1n) :: Gamma)) in H11 .
      all: auto using inclusion_refl, cons_shadow.
    + apply eqb_neq in Heqb as Hneq.
      apply T_LamAbs...
      apply Typing.weakening_term with (Delta' := Delta) (Gamma' := (x, U) :: (s, T1n) :: Gamma) in H11.
      all: auto using inclusion_refl, cons_permute...

  - admit. (* Constr *)
  - admit. (* Case *)
Admitted.

Corollary substitution_preserves_typing__Term : forall t Delta Gamma x U Un v T,
    Delta ,, ((x, U) :: Gamma)  |-+ t : T ->
    normalise U Un ->
    [] ,, [] |-+ v : Un ->
    Delta ,, Gamma |-+ <{ [x := v] t }> : T.
Proof. apply substitution_preserves_typing. Qed.

Corollary substitution_preserves_typing__Binding : forall b Delta Gamma rec x U Un v,
    Delta ,, ((x, U) :: Gamma) |-ok_b rec # b ->
    normalise U Un ->
    [] ,, [] |-+ v : Un ->
    Delta ,, Gamma |-ok_b rec # <{ [x := v]b b }>.
Proof. apply substitution_preserves_typing. Qed.
