Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.TypeSubstitution.

Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.BaseKindedness.
(* From PlutusCert Require Import util. *)

From PlutusCert Require Import FreeVars.

Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.FreeInContext.

Import PlutusNotations.

Require Import PlutusCert.Util.List.

Require Import PlutusCert.Util.

Require Import Lists.List.
Import ListNotations.

Require Import Coq.Strings.String.
Local Open Scope string_scope.

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
           (* destr_eqb_eq y x.
           ++ contradiction.
           ++ eapply IHGamma; eauto.  *)
           admit.
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

(* TODO: lemma name?

I Doubt this is true because of substituteTCA in normalise


 *)

Ltac destruct_match :=
  match goal with
  | H : (match ?X with _ => _ end = _ ) |- _ => destruct X eqn:?; try discriminate
  end.

(* Create cases for x = y and x <> y (where we move from (x =? y) = true -> x = y*)
Ltac destr_eqb_eq x y :=
  let H := fresh "H" in
  destruct (x =? y) eqn:H; [apply String.eqb_eq in H; subst | apply String.eqb_neq in H].

(* Richard: Not true, see schrift *)
Lemma substituteT__normalisation T Tn SubTn X U:
  normalise T Tn ->
  normalise (substituteT X U Tn) SubTn ->
  normalise (substituteT X U T) SubTn.
Proof.
  intros Hnorm__T Hnorm__SubTn.
  generalize dependent Tn.
  generalize dependent SubTn.
  induction T; intros.
  - inversion Hnorm__T; subst.
    simpl.
    (destr_eqb_eq X t).
    + (* X = t *)
      simpl in Hnorm__SubTn.
      rewrite eqb_refl in Hnorm__SubTn.
      assumption.
    + (* X <> t *)
      simpl in Hnorm__SubTn.
      apply eqb_neq in H.
      rewrite H in Hnorm__SubTn.
      assumption.
  - inversion Hnorm__T; subst.
    simpl.
    simpl in Hnorm__SubTn.
    inversion Hnorm__SubTn; subst.
    constructor; auto.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - admit.
  - admit.
  - admit.
  - admit.
  - (* Ty_App *)
    simpl.
    inversion Hnorm__T; subst.
    + (* N_BetaReduce *)
      simpl.
      remember H1 as H1'. clear HeqH1'.
      assert (exists SubT1n, normalise (substituteT X U (Ty_Lam bX K T1n)) (Ty_Lam bX K SubT1n)) as [SubT1n HSubLamN].
      {
        admit.
      }
      assert (exists SubT2n, normalise (substituteT X U T2n) SubT2n) as [SubT2n HSubT2n].
      {
        admit.
      }

      eapply IHT1 in H1; eauto.
      econstructor; eauto.
      (* subT X U T1n ==> SubT1n
        

        SubCA bX T2n T1n ==> Tn

        Sub X U Tn ==> SubTn

        ADMIT: Not so clear to me yet.
      *)
      admit.
    + (* N_App *)
      simpl.
      simpl in Hnorm__SubTn.
      (* ADMIT: I DONT KNOW *)

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

Locate ":[".

(* X is free in t *)
Definition t := TyInst (TyAbs "X0" KB (TyAbs "X" KB (Var "x"))) (Ty_Var "X").
Definition T := Ty_Forall (fresh "X0" (Ty_Var "X") <{ ℤ }>) KB <{ ℤ }>.

(*
  IDEA Jacco: rename approach in TyForall?
*)


(*
  Λ (X0: * ) (Λ (X :: * ) 3) @ X : SubstitueTCA X0 X  (∀ (X :: * ) Int)
*)

Definition U := Ty_Builtin DefaultUniBool.

(* THe problem is that here U gets substituted in the type immediately,
so then no ftvs are in the instantiated type anymore, so then no fresh variable
is gnerated
*)
Definition substA_t : term :=
  <{ :[ "X" := U ] t }>.

Lemma t_wt :
  (("X", Kind_Base)::nil),, [("x", <{ ℤ }>)] |-+ t : T. 
Proof.
  (* unfold t.
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
  constructor. constructor. *)
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
  (* rewrite H.
  assert (existsb (eqb "X") (ftv (U)) = false) by admit. (* no ftv in Bool *)
  unfold U in H0.
  rewrite H0.
  unfold T2.
  constructor.
  constructor. *)
Admitted.

(* We also know U is closed, but do not need it yet *)
Lemma commute_substituteT :
  forall X U V T,
    substituteT X U (substituteT X V T) = substituteT X (substituteT X U V) T.
Proof.
  intros X U V T.
  induction T.
  - simpl.
    destr_eqb_eq X t0; auto.
    simpl.
    apply eqb_neq in H; rewrite H; auto.
  - simpl.
    f_equal.
    apply IHT1; auto.
    apply IHT2; auto.
  - simpl.
    f_equal.
    apply IHT1; auto.
    apply IHT2; auto.
  - simpl.
    destr_eqb_eq X b; auto.
    simpl.
    rewrite String.eqb_refl; auto.
    simpl.
    apply eqb_neq in H; rewrite H; auto.
    f_equal.
    apply IHT; auto.
  - simpl. reflexivity.
  - simpl.
    destr_eqb_eq X b; auto.
    simpl.
    rewrite String.eqb_refl; auto.
    simpl.
    apply eqb_neq in H; rewrite H; auto.
    f_equal.
    apply IHT; auto.
  - simpl.
    f_equal.
    apply IHT1; auto.
    apply IHT2; auto.
Admitted.

Lemma substituteT_vacuous_closed X U T :
    Ty.closed T ->
    substituteT X U T = T.
Admitted.

(* NOTE: commute_sub_naive *)
Lemma commute_substituteT_2 :
  forall X X0 U V T,
    X <> X0 -> (* TODO: necessary? Maybe without it this implies commute_substituteT *)
    Ty.closed U ->
    (* TODO: Required: binders in T are not free in V? *)
    substituteT X0 (substituteT X U V) (substituteT X U T) = 
      substituteT X U (substituteT X0 V T).
Proof.
  intros X X0 U V T Hneq Uclosed.
  induction T.
  - simpl.
    destr_eqb_eq X t0; auto.
    + simpl.
      apply eqb_neq in Hneq.
      rewrite String.eqb_sym in Hneq; rewrite Hneq.
      simpl.
      rewrite String.eqb_refl; auto.
      apply substituteT_vacuous_closed; auto.
    + simpl.
      destr_eqb_eq X0 t0; auto.
      simpl.
      apply eqb_neq in H; rewrite H. reflexivity.
  - simpl.
    f_equal.
    apply IHT1; auto.
    apply IHT2; auto.
  - simpl.
    f_equal.
    apply IHT1; auto.
    apply IHT2; auto.
  - simpl.
    destr_eqb_eq X b; destr_eqb_eq X0 b; auto.
    + contradiction Hneq. reflexivity.
    + simpl.
      rewrite String.eqb_refl; auto.
      apply eqb_neq in H; rewrite H.
      f_equal.
      (* What if b in V? *)
      admit.
    + simpl.
      rewrite String.eqb_refl; auto.
      apply eqb_neq in H; rewrite H.
      f_equal.
    + simpl.
      apply eqb_neq in H; rewrite H.
      apply eqb_neq in H0; rewrite H0.
      rewrite IHT.
      reflexivity.
  - simpl. reflexivity.
  - (* Ty_Lam *)
    simpl.
    destr_eqb_eq X b; destr_eqb_eq X0 b; auto.
    + contradiction Hneq. reflexivity.
    + simpl.
      rewrite String.eqb_refl; auto.
      apply eqb_neq in H; rewrite H.
      f_equal.
      (* What if b in V? *)
      admit.
    + simpl.
      rewrite String.eqb_refl; auto.
      apply eqb_neq in H; rewrite H.
      f_equal.
    + simpl.
      apply eqb_neq in H; rewrite H.
      apply eqb_neq in H0; rewrite H0.
      rewrite IHT.
      reflexivity.
  - (* Ty_App *)
    simpl.
    f_equal.
    apply IHT1; auto.
    apply IHT2; auto.
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
  all: try (intros Delta Gamma rec X K U Htyp__b Hkind__U).
  all: try (inversion Htyp__t; subst).
  - (* Let (NonRec) *)
    simpl.
    econstructor; eauto.
    + admit.
    + (* probably *) admit.
    + 
       destruct (existsb (eqb X) (btvbs bs)).
      * (* X in btvbs bs *)
        simpl.
        (* Everything gets renamed accordingly, should hold?*)
        admit.
      * (* X not in btvbs bs *)
        assert (@substA_bnr' substA_b X U bs = bs).
        {
          (* ADMIT: I think this is true, but not sure yet *)
          admit.
        }
        rewrite H1.
        (* hmm. Then X should also not be appearing in Gamma *)
        unfold P_Term in H0.
        (* eapply H0. TODO: Cannot apply it because bsGn is in front of the gsubst. we can probably drag it inside *)
        admit.
    + (* I think the key here is that there is no longer an X in substituteT X U T. *)
      admit.
  - (* Let Rec *)
    admit.
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
      destr_eqb_eq s Y.
      * (* Y = s = X *)
        assert (Hsub2: substituteT Y (Ty_Var Y) Tn0 = Tn0) by admit.
        inversion Hnorm__Tn; subst.
        assert (Hsub3: substituteT Y (Ty_Var Y) T0n = T0n) by admit.
        rewrite <- Hsub3.
        apply T_TyAbs; auto.
        -- admit.
        -- admit.
        -- 
          (* Y not in btv T0n??? But normalise could create them!!! No, because Tn0 is already
            normal and normal stable *)
          admit.
      * (* Y <> s   and X = s*)
        inversion Hnorm__Tn; subst.
        assert (substituteT s U (substituteT s (Ty_Var Y) Tn0) = substituteT s (Ty_Var Y) Tn0) by admit. (* vac sub*)
        (* Also sub t Y Tn0 is normal, by Y fresh and Tn0 normal*)
        rewrite H1 in H6.
        assert (T0n = substituteT s (Ty_Var Y) Tn0) by admit.
        rewrite H2.
        apply T_TyAbs; auto.
        -- (* Some drop_ty_var arguments *) admit.
    + destr_eqb_eq s Y.
      * (* s = Y   and X <> s *) 
        simpl in Hnorm__Tn.
        rewrite <- String.eqb_neq in H0.
        rewrite H0 in Hnorm__Tn.
        inversion Hnorm__Tn; subst.
        assert (T0n = substituteT Y (Ty_Var Y) T0n) by admit.
        rewrite H1.
        eapply T_TyAbs; auto.
        -- admit.
        -- (* no ftvs created, U closed, etc.*)
           admit.
        -- (* ADMIT: We assume now that normalise does not create new ftvs (but it can)!*)
           admit.
      * (* s <> Y and X <> s*)

        (* X = Y, then we have no substituteT in types. 
           On term level?
        *)
        simpl in Hnorm__Tn.
        destr_eqb_eq X Y.
        -- (* X = Y *)
           unfold P_Term in H.
           inversion Hnorm__Tn; subst.
           assert (substituteT s (Ty_Var Y) Tn0 = T0n) by admit. (* ADMIT: Not true, assume normality = equality*)
           rewrite <- H2.
           constructor; auto.
           assert (drop_ty_var Y (gsubst Y U Gamma) = gsubst Y U Gamma).
           {
             (* ADMIT: I think this is true, but not sure yet *)
             admit.
           }
           rewrite H3.
           rewrite drop_ty_var__gsubst; auto.
           {
            eapply H with (T := Tn0) (K := K); eauto.
            - (* By drop_ty_var inclusion? and weakening?
                drop_ty_var Y Gamma included in Gamma

                Then drop s (drop Y Gamma) included in Gamma
            *)
            
            
              (* ADMIT: Weakening permute *) admit.
            - (* Y not in Tn0, so vacuous subst, so yes *) admit.
           }
           ++ (* U closed *) admit.



        -- (* s, X, Y disctinct *)
           inversion Hnorm__Tn; subst.
           (* Let's assume for now that it is already normal: *)
           assert (substituteT X U (substituteT s (Ty_Var Y) Tn0) = substituteT s (Ty_Var Y) (substituteT X U Tn0)) by admit.
           rewrite H3 in H10.
           assert (T0n = substituteT s (Ty_Var Y) (substituteT X U Tn0)) by admit.
           rewrite H4.
           constructor; auto.
           ++ unfold P_Term in H. clear H3 H4.
              rewrite drop_ty_var__gsubst; auto.
              rewrite drop_ty_var__gsubst; auto.
              eapply H with (T := Tn0) (K := K); eauto.
              ** (* ADMIT: Weakening permute *) admit.
              ** (* ADMIT: We forget about normalisation for now *) admit.
              ** (* U closed*) admit.
              ** (* U closed *) admit.
          ++ (* normalise does not create new ftvs and U clsoed *)admit.
          ++ (* ADMIT: We assume now that normalise does not create new btvs (but it can)!*)
             admit.

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
    (* Probably: 
    ADMIT:
      closed (lookupBuildtinTy d)
        Then closed T, but also lookupBuiltinTy d = T.
        Then substituteT X U T = T.
        Then normalise T Tn => T = Tn.
     *)
     assert (T = Tn) by admit.
     subst.
     econstructor; eauto.
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

        assert (normalise
          (substituteTCA X0 (substituteT X0 U t1) T1n)
          (substituteT X0 U (substituteTCA X0 t1 T1n))
            = normalise
          (substituteT X0 (substituteT X0 U t1) T1n)
          (substituteT X0 U (substituteT X0 t1 T1n))
        ).
        {        (* 
          ADMIT: What if we have substituteT instead of substituteTCA, is it true then?
          Yes.
        *)
          admit.
        }
        rewrite H0.
        erewrite commute_substituteT.
        (* ADMIT: They are identical, but the latter does not need to be normal yet. I think that is
            solved by not doing all thsoe admits above
          *)


        admit.
    + (* X <> X0 *)
      assert (exists subT1n, normalise (substituteT X U t1) subT1n) as [subT1n HsubT1n].
        {
          eapply strong_normalisation; eauto.
          apply has_type__basekinded in H2.
          inversion H2; subst.
          eauto.
          eapply substituteT_preserves_kinding; eauto.
      }

      assert (exists SubT1nn, normalise (substituteT X U T1n) SubT1nn) as [SubT1nn HT1nn].
      {
        eapply strong_normalisation; eauto.
        apply has_type__basekinded in H2.
        inversion H2; subst.
        eauto.
        eapply substituteT_preserves_kinding; eauto.
        eapply Kinding.weakening; eauto.
        admit.
        (* apply inclusion_swap; eauto. *)
      } 

      econstructor.
      * eapply H; eauto.
        simpl substituteT.
        apply eqb_neq in H0.
        rewrite H0.
        constructor; eauto.
      * eapply substituteT_preserves_kinding; eauto.
      * eauto.
      * (* ADMIT: Just like above for now equating all the normal stuff: *)
        assert (t1 = T2n) by admit; subst.
        assert (substituteT X U T2n = subT1n) by admit; subst.
        assert (substituteT X U T1n = SubT1nn) by admit; subst.
        assert (substituteTCA X0 T2n T1n = T) by admit; subst.
        clear HT1nn HsubT1n H8 H6.
        assert (substituteT X U (substituteTCA X0 T2n T1n) = Tn) by admit; subst.
        clear Hnorm__Tn.

        (* Aha, so it is not the same as above, X <> X0 *)

        (* We want to call commute_substituteT_2 with V := T2n, and with T := T1n
            And we need: btv in T not free in V
              That is like exactly NC T [? -> V] from the alpha stuff
            
          If we change the TyInst rule as I suggested to Jacco:
          typechecking the rhs of TyInst with smaller Delta,
            then we have this assumption I think
        *)
         admit.
  - (* Error *)
    (* ADMIT: Probably we do not need to do this for Error since we are not doing preservation for non-error*)
    admit.
  - (* IWrap *)
    simpl.
    simpl in Hnorm__Tn.
    inversion Hnorm__Tn; subst.
    assert (exists subTXUT0n, normalise (substituteT X U T0n) subTXUT0n) as [subTXUT0n HsubTXUT0n].
    {
      eapply strong_normalisation; eauto.
      admit.
    }

    eapply T_IWrap with (T0n := subTXUT0n).
    + eapply substituteT_preserves_kinding; eauto.
    + eapply substituteT__normalisation; eauto.
    + eapply substituteT_preserves_kinding; eauto.
    + eapply substituteT__normalisation; eauto.
    + (* ADMIT: not sure yet, but probably some more convoluted case of substituteT__normalisation 
      *)
      admit.
    + eapply H; eauto.
  - (* Unwrap *)
    assert (exists sub_XU_Tn0, normalise (substituteT X U Tn0) sub_XU_Tn0) as [sub_XU_Tn0 Hsub_XU_Tn0].
    {
      eapply strong_normalisation; eauto.
      eapply substituteT_preserves_kinding; eauto.
    }
    remember H1 as H1'. clear HeqH1'.
    eapply has_type__basekinded in H1'; eauto.
    inversion H1'; subst.
    assert (exists sub_XU_Fn, normalise (substituteT X U Fn) sub_XU_Fn) as [sub_XU_Fn Hsub_XU_Fn].
    {
      eapply strong_normalisation; eauto.
      eapply substituteT_preserves_kinding; eauto.
    }
    simpl.
    eapply T_Unwrap.
    + eapply H; eauto.
      simpl.
      constructor; eauto.
    + admit.
    + (* ADMIT: Not sure yet *)
    admit.
  - (* TermBind *)
    simpl.
    destruct v.
    inversion Htyp__b; subst.
    assert (exists sub_XU_Tn, normalise (substituteT X U t1) sub_XU_Tn) as [sub_XU_Tn H_sub_XU_Tn].
    {
      eapply strong_normalisation; eauto.
      eapply substituteT_preserves_kinding; eauto.
    }
    econstructor.
    + eapply substituteT_preserves_kinding; eauto.
    + eauto.
    + eapply H; eauto.
      (* ADMIT: 
         
         norm t1 Tn
         norm (sub X U t1) sub_XU_Tn
         =>
         norm (sub X U Tn) sub_XU_Tn 
      *)
      admit.
  - (* TypeBind *)
    simpl.
    inversion Htyp__b; subst.
    econstructor.
    eapply substituteT_preserves_kinding; eauto.
  - (* DatatypeBind *)
    simpl.
    destruct dtd.
    inversion Htyp__b; subst.
    inversion H0; subst; clear H0.
    simpl in *.
    destruct rec.
    + (* NonRec *)

      (* ADMIT: No time to finish this*)
      admit.
    + (* Rec *)
      econstructor; eauto.
      * admit.
      * intros.
        simpl.
        (* [X := U]cs cs must contain Vardecls*)
        induction cs; [inversion H|].
        simpl in H.
        destruct a.
        destruct H.
        -- subst.
           simpl.
           econstructor.
           3: eauto.
           ++ admit.
           ++ admit.
        -- eapply IHcs; eauto.
           ++ (* uhm*) admit.
           ++ (* NODUP smaller *) admit.
           ++ (* hmmm, not getting closer *)
            admit.
      * simpl.
        (* ADMIT: How can this be true? We must know XK already in Delta?
          This seems to be problematic in the special case where the variable we are substituting (X)
          is equal to the datatype name.

          Probably indeed the datatype name should not be renamed (it is like a tyabs binder), but
          how to reconcile XK = X?

          We should know from bindings_well_formed_rec that X is already in Delta
          But even then, this creates weird things, for instance if K is of a different kind then what
          it has in Delta.
        *)
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