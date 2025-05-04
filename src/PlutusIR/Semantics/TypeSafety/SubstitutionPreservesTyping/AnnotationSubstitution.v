Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.TypeSubstitution.

Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.BaseKindedness.
From PlutusCert Require Import util.

Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.FreeInContext.

Import PlutusNotations.

Require Import PlutusCert.Util.List.

Require Import Lists.List.
Import ListNotations.

Require Import Coq.Logic.FunctionalExtensionality.

Definition gsubst (a : string) (T' : ty ) (Gamma : list (string * ty)) :=
  map (fun '(x, T) => (x, substituteT a T' T)) Gamma.

Lemma gsubst_empty : forall X U,
    gsubst X U [] = [].
Proof.
  intros X U.
  unfold gsubst.
  simpl.
  reflexivity.
Qed.

Lemma gsubst__substituteT Gamma x X U T :
    lookup x Gamma = Datatypes.Some T ->
    lookup x (gsubst X U Gamma) = Datatypes.Some (substituteT X U T).
Proof with auto.
  induction Gamma.
  all: intros H; unfold gsubst.
  - inversion H.
  - destruct a.
    destruct (string_dec x s).
    + subst s.
      simpl.
      rewrite eqb_refl.
      rewrite lookup_eq in H.
      congruence.
    + rewrite lookup_neq in H...
      apply eqb_neq in n.
      rewrite eqb_sym in n.
      simpl.
      rewrite n...
Qed.

(* By drop_ty_var, X not in Ty.ftv T*)
Lemma gsubst__drop_ty_var__substituteT Gamma x X U T :
    Ty.closed U ->
    lookup x (drop_ty_var X Gamma) = Datatypes.Some T ->
    lookup x (drop_ty_var X (gsubst X U Gamma)) = Datatypes.Some T.
Proof with auto.
  intros Hclosed Hl.
  unfold drop_ty_var in *.
  remember ([]) as R.
  clear HeqR.
  generalize dependent R.
  induction Gamma; intros.
  - simpl in Hl. inversion Hl.
  - destruct a as [y V].
    simpl.
    destruct (in_dec string_dec X (Ty.ftv (substituteT X U V))).
    + (* X in substT X U V *)
      destruct (in_dec string_dec X (Ty.ftv V)).
      * (* X in V *)
        eapply IHGamma.
        (* 
          ADMIT ( *** ):
          by lookup x (drop_ty_var X (y, V)::Gamma) = Some T,
          we know lookup x (drop_ty_var' X Gamma [y]) = Some T 

          (* Then we know x <> y*)
          Then also lookup x (drop_ty_var X Gamma) = Some T
        *)
        admit.
      * (* X not in V *)
        exfalso.
        (* ADMIT: X in substT X U V, but U is closed, so X in V. *)
        admit.
    + (* X not in substT X U V *)
      destruct (in_dec string_dec X (Ty.ftv V)).
      * (* X in V *)
        assert (x <> y).
        {
        (* ADMIT: X in V, then lookup x (drop_ty_var X ((x, V)) should be None as all keys x will be removed)*)
        admit.
        }
        assert (lookup x (drop_ty_var' X Gamma R) = Some T).
        {
          (* See ADMIT ( *** ) *) admit.
        }
        destruct (in_dec string_dec y R).
        -- eapply IHGamma; eauto. 
        -- simpl.
           destr_eqb_eq y x.
           ++ contradiction.
           ++ eapply IHGamma; eauto. 
      * (* X not in V *)
        assert (lookup x (drop_ty_var' X Gamma R) = Some T).
        {
          (* See ADMIT ( *** ) *) admit.
        }
        destruct (in_dec string_dec y R).
        -- eapply IHGamma; eauto.
        -- simpl.
           assert (x <> y).
           {
             (* ADMIT: x <> y, then lookup x (drop_ty_var X ((x, V)) should be None as all keys x will be removed*)
             admit.
           }
           apply String.eqb_neq in H0.
           rewrite String.eqb_sym in H0.
           rewrite H0.
           eapply IHGamma; eauto.

  (* ADMIT: See comments *)
Admitted.

Lemma gsubst_absorbs_substituteT : forall x X U T Gamma,
    ((x, (substituteT X U T)) :: gsubst X U Gamma) = gsubst X U ((x, T) :: Gamma).
Proof.
  reflexivity.
Qed.

Lemma drop_ty_var__gsubst s X U Γ : 
  s <> X ->
  Ty.closed U ->
  drop_ty_var s (gsubst X U Γ) = gsubst X U (drop_ty_var s Γ).
Proof.
  intros Hneq Hclosed.
  unfold drop_ty_var.
  remember ([]) as R.
  clear HeqR.
  generalize dependent R.
  induction Γ; intros.
  - simpl.
    reflexivity.
  - destruct a as [x T].
    simpl.
    destruct (in_dec string_dec s
      (Ty.ftv
      (substituteT X U T))).
    + destruct (in_dec string_dec s (Ty.ftv T)).
      * eapply IHΓ.
      * exfalso.
        (* ADMIT: s in substT X U T, but U is closed, so s in T. *)
        admit.
    + 
      destruct (in_dec string_dec s (Ty.ftv T)).
      * exfalso.
        (* ADMIT: s not in substT X U T 
                  by s <> X, then s not in T *)
        admit.
      * destruct (in_dec string_dec x R).
        -- eapply IHΓ.
        -- rewrite <- gsubst_absorbs_substituteT.
           f_equal.
           eapply IHΓ.
(* ADMIT: See comments *)    
Admitted.

(* TODO: lemma name? *)
Lemma substituteT__normalisation T Tn SubTn X U:
  normalise T Tn ->
  normalise (substituteT X U Tn) SubTn ->
  normalise (substituteT X U T) SubTn.
Proof.

Admitted.

(** ** Predicates *)
Definition P_Term (t : term) :=
  forall Delta Gamma X K U T Tn,
    ((X, K) :: Delta) ,, Gamma |-+ t : T ->
    [] |-* U : K ->
    normalise (substituteT X U T) Tn ->
    Delta ,, (gsubst X U Gamma) |-+ <{ :[X := U] t }> : Tn.

Local Open Scope string_scope.
Local Open Scope list_scope.

Definition KB := Kind_Base.

(* X is free in t *)
Definition t := TyInst (TyAbs "X0" KB (TyAbs "X" KB (Var "x"))) (Ty_Var "X").
Definition T := Ty_Forall (fresh "X0" (Ty_Var "X") <{ ℤ }>) KB <{ ℤ }>.

Definition U := Ty_Builtin DefaultUniBool.

Definition substA_t : term :=
  <{ :[ "X" := U ] t }>.

Lemma t_wt :
  (("X", Kind_Base)::nil),, [("x", <{ ℤ }>)] |-+ t : T. 
Proof.
  unfold t.
  unfold T.
  repeat econstructor; eauto.
  autorewrite with substituteTCA.
  assert ("X0" <> "X") by admit. (* ADMIT: non-identical strings*)
  apply eqb_neq in H.
  rewrite H.
  assert (existsb (eqb "X") (ftv (Ty_Var "X")) = true) by admit. (* ADMIT: "X" = "X"*)
  rewrite H0.
  simpl.
  assert (Hren_builtin: (rename "X"
  (fresh "X0" (Ty_Var "X") <{ ℤ }>)
  <{ ℤ }>) = <{ ℤ }>) by admit. (* ADMIT: no ftvs in TInt to rename *)
  rewrite Hren_builtin; clear Hren_builtin.
  autorewrite with substituteTCA.
  constructor. constructor.
Admitted.

Definition T2 := Ty_Forall "X" KB <{ ℤ }>.

Lemma substA_t_wt :
  [] ,, [("x", <{ ℤ }>)] |-+ substA_t : T2.
Proof.
  unfold substA_t.
  unfold T.
  simpl.
  repeat econstructor; eauto.
  autorewrite with substituteTCA.
  assert ("X0" <> "X") by admit. (* ADMIT: non-identical strings*)
  apply eqb_neq in H.
  rewrite H.
  assert (existsb (eqb "X") (ftv (U)) = false) by admit. (* no ftv in Bool *)
  unfold U in H0.
  rewrite H0.
  unfold T2.
  constructor.
  constructor.
Admitted.
  

Definition P_Binding (b : binding) : Prop :=
  forall Delta Gamma rec X K U,
    ((X, K) :: Delta) ,, Gamma |-ok_b rec # b ->
    [] |-* U : K ->
    Delta ,, (gsubst X U Gamma) |-ok_b rec # <{ :[X := U]b b }>.

#[export] Hint Unfold
  P_Term
  P_Binding
  : core.

Theorem substA_preserves_typing :
  forall t, P_Term t.
Proof with (eauto using substituteT_preserves_kinding with typing).
  apply term__ind with P_Binding.
  all: intros.
  all: unfold P_Term.
  all: try (intros Delta Gamma X K U T Tn Htyp__t Hkind__U Hnorm__Tn).
  all: unfold P_Binding.
  all: try (intros Delta Gamma X K U Htyp__b Hkind__U).
  all: try (inversion Htyp__t; subst).
  - admit.
  - admit.
  - (* Var *)
    simpl.
    econstructor.
    + eapply gsubst__substituteT; eauto.
    + eapply substituteT_preserves_kinding; eauto.
    + eapply substituteT__normalisation; eauto.
  - (* TyAbs *)
    simpl.
    destr_eqb_eq X s.
    + (* X = s *)
      simpl substituteT in Hnorm__Tn.
      rewrite eqb_refl in Hnorm__Tn.
      inversion Hnorm__Tn; subst.
      constructor.
      assert (Tn0 = T0n).
      {
        apply has_type__normal in H6.
        eapply normalisation__stable__normal; eauto.
      }
      subst.
       eapply Typing.weakening; eauto.
       * apply inclusion_shadow_left.
       * unfold inclusion.
         intros.
         erewrite gsubst__drop_ty_var__substituteT; eauto.
         eapply Ty.kindable_empty__closed; eauto.
    + simpl substituteT in Hnorm__Tn.
      apply eqb_neq in H0.
      assert (X <> s) by now apply eqb_neq in H0.
      rewrite H0 in Hnorm__Tn.
      inversion Hnorm__Tn; subst.
      constructor.
      unfold P_Term in H.
      rewrite drop_ty_var__gsubst; auto.
      * eapply H; eauto.
        eapply Typing.weakening; eauto.
        -- apply inclusion_swap; eauto.
        -- apply inclusion_refl.
      * eapply Ty.kindable_empty__closed; eauto.

  - (* LamAbs *)
    simpl.
    simpl substituteT in Hnorm__Tn.
    inversion Hnorm__Tn; subst.
    constructor; auto.
    * eapply substituteT_preserves_kinding; eauto.
    * eapply substituteT__normalisation; eauto.
    * assert ((s, substituteT X U T1n) :: gsubst X U Gamma = gsubst X U ((s, T1n) :: Gamma)).
      {
        rewrite gsubst_absorbs_substituteT; auto.
      }
      assert (Hgsubst_not_normal: 
        (s, (substituteT X U T1n)) :: (gsubst X U Gamma) = 
          (s, T1n0) :: gsubst X U Gamma).
      {
      (* ADMIT: substituteT X U T1n may not be normal, 
          how to reconcile? Must gsubst also normalise? 
          Maybe find counterexample tomorrow.

          Or does typing context not have to be normal?
          Something like, if it is well_typed for T in gamma,
          then it is well_typed for Tn in gamma.
          *)
          admit.
      }
      rewrite <- Hgsubst_not_normal.
      unfold P_Term in H.
      rewrite H0.
      eapply H; eauto.
  - (* Apply *)
    simpl.
    assert (Delta |-* (substituteT X U T1n) : Kind_Base).
    {
      eapply substituteT_preserves_kinding; eauto.
      eapply has_type__basekinded; eauto.
    }
    eapply strong_normalisation in H1 as [subT1n HsubT1n].
      
    econstructor.
    + 
      eapply H; eauto.
      simpl substituteT.
      constructor; eauto.
    + eapply H0; eauto.
  - (* Constant *)
    simpl.
    inversion Hnorm__Tn; subst.
    constructor.
  - (* Builtin *)
    simpl.
    (* ADMIT: UHM, probably not difficult? *)
    admit.
  - (* TyInst *)
    simpl.
    unfold P_Term in H.
    destr_eqb_eq X X0.
    + (* X = X0 *)
      assert (exists T1nn, normalise T1n T1nn) as [T1nn HT1nn].
      {
        eapply strong_normalisation; eauto.
        apply has_type__basekinded in H2.
        inversion H2; subst.
        eauto.
      } 
      assert (exists subt0, normalise (substituteT X0 U t1) subt0) as [subt0 Hsubt0].
        {
          eapply strong_normalisation; eauto.
          apply has_type__basekinded in H2.
          inversion H2; subst.
          eauto.
          eapply substituteT_preserves_kinding; eauto.
      }

      econstructor.
      * eapply H; auto.
        simpl substituteT.
        -- eauto.
        -- assumption.
        -- simpl substituteT.
           rewrite eqb_refl.
           constructor; eauto.
      * eapply substituteT_preserves_kinding; eauto.
      * eauto.
      * (*
        We know:   normalise (substituteT X0 U T) Tn
         and       normalise (substituteTCA X0 T2n T1n) T.

         Hence     normalise (substituteT X0 U (subsituteTCA X0 T2n T1n)) Tn.      

         Also   normalise T1n T1nn
          Hence     normalise (substituteT X0 U (subsituteTCA X0 T2n T1nn)) Tn.

          So let us simplify the argument by (wrongly) equating normal stuff
        *)
        assert (T1nn = T1n) by admit. clear HT1nn. subst.
        assert (T2n = t1) by admit. clear H6. subst.
        assert (subt0 = substituteT X0 U t1) by admit. clear Hsubt0. subst.
        assert (Tn = substituteT X0 U T) by admit. clear Hnorm__Tn. subst.
        assert (T = (substituteTCA X0 t1 T1n)) by admit. clear H8. subst.
        (* Is that true? I fear alpha equivalence.
          Create some examples.
          It is not.
        *)


        admit.
    + (* X <> X0 *)
      assert (exists SubT1nn, normalise (substituteT X U T1n) SubT1nn) as [SubT1nn HT1nn].
      {
        eapply strong_normalisation; eauto.
        apply has_type__basekinded in H2.
        inversion H2; subst.
        eauto.
        eapply substituteT_preserves_kinding; eauto.
        eapply Kinding.weakening; eauto.
        apply inclusion_swap; eauto.
      } 

      econstructor.
      * eapply H; eauto.
        simpl substituteT.
        apply eqb_neq in H0.
        rewrite H0.
        constructor; eauto.
      * admit.
      * admit.
      * admit.
  - (* Error *)
    admit.
  - (* IWrap *)
    admit.
  - (* Unwrap *)
    admit.
  - (* Constr *)
    admit.
  - (* Case *)
    admit.
  - (* TermBind *)
    admit.
  - (* TypeBind *)
    admit.
  - (* DatatypeBind *)
    admit.
  
(* ADMIT: I had no time to finish this. Should follow from uniqueness property, amongst others. *)
Admitted.

Corollary substA_preserves_typing__Term : 
  forall Delta Gamma X K U t T Tn,
    ((X, K) :: Delta) ,, Gamma |-+ t : T ->
    [] |-* U : K ->
    normalise (substituteT X U T) Tn ->
    Delta ,, (gsubst X U Gamma) |-+ <{ :[X := U] t }> : Tn.
Proof.
  intros.
  eapply substA_preserves_typing; eauto.
Qed.

Corollary substA_preserves_typing__Term__value : 
  forall X K U t T Tn,
    ((X, K) :: nil) ,, nil |-+ t : T ->
    [] |-* U : K -> (* 
    
      So.. no capture?
      No free vars in U, hence a binder in T cannot capture that

    *)
    normalise (substituteT X U T) Tn ->
    nil ,, nil |-+ <{ :[X := U] t }> : Tn.
Proof.
  intros.
  assert (nil ,, (gsubst X U nil) |-+ <{ :[X := U] t }> : Tn).
  {
    eapply substA_preserves_typing__Term; eauto.
  }
  simpl in H2.
  auto.
Qed.