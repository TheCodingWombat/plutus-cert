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
    admit.
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
    admit.
  - (* Builtin *)
    admit.
  - (* TyInst *)
    admit.
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