
From Equations Require Import Equations.
Require Import Coq.Lists.List.
Local Open Scope list_scope.

Require Import Lia.

Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Ascii.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Wf_nat.

From PlutusCert Require Import SN_STLC_GU SN_STLC_nd util Util.List STLC STLC_Kinding. 
From PlutusCert Require Import PlutusIR Checker.
From PlutusCert Require Static.TypeSubstitution Type_reduction.

Set Printing Implicit.

(* from PIR to annotated stlc*)
Fixpoint f (t : ty) : STLC.term :=
  match t with
  | Ty_Var x => tmvar x
  | Ty_Lam x A t => @tmabs Lam x A (f t)
  | Ty_Forall x A t => @tmabs ForAll x A (f t)
  | Ty_Fun t1 t2 => @tmbin Fun (f t1) (f t2)
  | Ty_App t1 t2 => @tmbin App (f t1) (f t2)
  | Ty_IFix f1 t1 => @tmbin IFix (f f1) (f t1)
  | Ty_SOP Tss => 
  (* Two fold rights instead of concat/map to help termination checking*)
      fold_right (fun Ts acc => 
        (fold_right (fun T acc2 => @tmbin Fun (f T) acc2) acc Ts))
        (tmbuiltin PlutusIR.DefaultUniInteger) Tss
      (* Instead of checking for the length, we just start with something of Base Kind*)
  | Ty_Builtin d => tmbuiltin d
  end.

Lemma f_preserves_rename s fr T :
  rename s fr (f T) = f (TypeSubstitution.rename s fr T).
Proof.
  unfold rename; unfold TypeSubstitution.rename.
  apply PlutusIR.ty__ind with (P := fun T => rename s fr (f T) = f (TypeSubstitution.substituteT s (PlutusIR.Ty_Var fr) T)); intros.
  all: try solve [simpl; f_equal; auto]. (* all cases without binders or lists *)
  all: try solve [simpl; destr_eqb_eq s X; try rewrite mren_id; simpl; f_equal; auto]. (* all cases with binders/vars *)
  induction H; auto.
  induction H; auto.
  simpl in IHForall. simpl. rewrite H. f_equal.
  apply IHForall0.
Qed.

Lemma f_preserves_ftv T :
  ftv (f T) = TypeSubstitution.ftv T.
Proof.
  apply PlutusIR.ty__ind with (P := fun T => ftv (f T) = TypeSubstitution.ftv T); intros.
  all: try solve [simpl; f_equal; auto]. 
  induction H; auto; simpl.
  induction H; auto; simpl.
  rewrite <- app_assoc.
  f_equal; auto.
Qed.

Lemma f_preserves_tv T :
  tv (f T) = TypeSubstitution.plutusTv T.
Proof.
  apply PlutusIR.ty__ind with (P := fun T => tv (f T) = TypeSubstitution.plutusTv T); intros.
  all: try solve [simpl; f_equal; auto]. 
  induction H; auto; subst.
  induction H; auto; subst; simpl.
  rewrite <- app_assoc.
  f_equal; auto.
Qed.

Lemma f_preserves_fresh2 y s' T :
  fresh2 ((y, f s')::nil) (f T) = TypeSubstitution.fresh y s' T.
Proof.
  simpl.
  unfold fresh2.
  unfold TypeSubstitution.fresh.
  rewrite f_preserves_tv.
  assert (Htv_keys_env: (tv_keys_env
    [(y, f s')] = (y :: (TypeSubstitution.plutusTv s')))).
  {
    unfold tv_keys_env.
    f_equal.
    rewrite f_preserves_tv.
    rewrite app_nil_r.
    reflexivity.
  }
  rewrite Htv_keys_env.
  f_equal.
  rewrite string_concat_app.
  rewrite string_concat_cons.
  rewrite string_app_assoc.
  auto.
Qed.

Lemma f_preserves_substituteTCA X U T :
  (f (TypeSubstitution.substituteTCA X U T)) = (substituteTCA X (f U) (f T)).
Proof.
  (* Uses induction the size of STLC terms*)
  remember (f T) as fT.
  remember (size fT) as n.
  generalize dependent fT.
  generalize dependent T.
  induction n using lt_wf_ind.
  intros.
  dependent induction fT; subst.
  + (* tmvar *)
    induction T; subst; inversion HeqfT; subst.
    autorewrite with substituteTCA.
    destr_eqb_eq X t; auto.
    (* With the current f definition, we have a not so nice inversino procedure *)
    exfalso.
    simpl in HeqfT.
    induction l.
    * inversion HeqfT.
    * induction a.
      -- simpl in HeqfT. eapply IHl; auto.
      -- eapply IHa; inversion HeqfT; auto.
  + (* tmabs *)
    induction T; subst; inversion HeqfT; subst.
    
    {
      autorewrite with substituteTCA.
      destr_eqb_eq X b; eauto.
      rewrite <- (f_preserves_ftv).
      destruct (existsb (String.eqb b) (ftv (f U))) eqn:Heq.
      -- simpl.
         remember (fresh2 _ _) as fr.
         remember (TypeSubstitution.fresh _ _ _) as fr'.
         assert (Hfr_pres: fr' = fr).
         {
           subst.
           symmetry.
           assert (tmvar b = f (PlutusIR.Ty_Var b)).
           {
             simpl.
             auto.
           }
           eapply f_preserves_fresh2.
         }
         rewrite Hfr_pres.
         f_equal.
         ++ eapply H; eauto.
           ** rewrite <- rename_preserves_size.
              simpl.
              lia.
           ** apply f_preserves_rename.
      -- simpl.
         f_equal.
         eapply H; eauto. simpl. lia.
    }


  (* TODO: EXACTLY IDENTICAL TO ABOVE*)

     {
      autorewrite with substituteTCA.
      destr_eqb_eq X b; eauto.
      rewrite <- (f_preserves_ftv).
      destruct (existsb (String.eqb b) (ftv (f U))) eqn:Heq.
      -- 
          simpl.
          remember (fresh2 _ _) as fr.
          remember (TypeSubstitution.fresh _ _ _) as fr'.
          assert (Hfr_pres: fr' = fr).
          {
            (* Not currently true, but probably possible to change on both sides*)
            subst.
            symmetry.
            assert (tmvar b = f (PlutusIR.Ty_Var b)).
            {
              simpl.
              auto.
            }
            eapply f_preserves_fresh2.
          }
          rewrite Hfr_pres.
          f_equal.
          ++ eapply H; eauto.
            ** rewrite <- rename_preserves_size.
               simpl.
               lia.
            ** apply f_preserves_rename.
      -- simpl.
         f_equal.
          eapply H; eauto. simpl. lia.
    }

    (* Again a new case because of Ty_SOP*)
    induction l; simpl in H1; inversion H1.
    induction a; simpl in H2; inversion H2.
    assert (f
      (TypeSubstitution.substituteTCA X U
      (PlutusIR.Ty_SOP ([] :: l))) = f
      (TypeSubstitution.substituteTCA X U
      (PlutusIR.Ty_SOP (l)))).
    {
      autorewrite with substituteTCA. simpl. reflexivity.
    }
    rewrite H0; clear H0.
    eapply IHl; intros; auto.
    inversion Heqn. lia.
         
    
  + (* tmbin *)
    induction T; subst; inversion HeqfT; subst.
    * autorewrite with substituteTCA; simpl; f_equal; eauto; eapply H; auto; simpl; lia. 
    * autorewrite with substituteTCA; simpl; f_equal; eauto; eapply H; auto; simpl; lia. 
    * autorewrite with substituteTCA; simpl; f_equal; eauto; eapply H; auto; simpl; lia. 
    * (* The interesting SOP case*)
       induction l; subst.
       -- inversion HeqfT. 
       -- induction a; subst.
          ++ simpl.
             assert (f
            (TypeSubstitution.substituteTCA X U
            (PlutusIR.Ty_SOP ([] :: l))) = f
            (TypeSubstitution.substituteTCA X U
            (PlutusIR.Ty_SOP (l)))).
            {
              autorewrite with substituteTCA.
              simpl.
              auto.
            }
            rewrite H0; clear H0.
            eapply IHl; intros; auto.
            ** inversion Heqn. lia.
            ** inversion Heqn. lia.
          ++ autorewrite with substituteTCA.
             simpl.
             inversion HeqfT; subst.
             f_equal.
             ** eauto.
                eapply H; eauto; simpl. lia.
             ** assert (@fold_right STLC.term PlutusIR.ty
                  (fun (T : PlutusIR.ty) (acc2 : STLC.term) =>
                @tmbin Fun (f T) acc2)
                  (@fold_right STLC.term (list PlutusIR.ty)
                  (fun (Ts : list PlutusIR.ty) (acc : STLC.term) =>
                @fold_right STLC.term PlutusIR.ty
                  (fun (T : PlutusIR.ty) (acc2 : STLC.term) =>
                @tmbin Fun (f T) acc2)
                  acc
                  Ts)
                  (tmbuiltin PlutusIR.DefaultUniInteger)
                  (@TypeSubstitution.map' (list PlutusIR.ty)
                  (list PlutusIR.ty) l
                  (fun (y : list PlutusIR.ty) (_ : y ∈ l) =>
                @TypeSubstitution.map' PlutusIR.ty
                  PlutusIR.ty y
                  (fun (T : PlutusIR.ty) (_ : T ∈ y) =>
                TypeSubstitution.substituteTCA X U T))))
                  (@TypeSubstitution.map' PlutusIR.ty PlutusIR.ty
                  a0
                  (fun (y : PlutusIR.ty) (_ : y ∈ a0) =>
                TypeSubstitution.substituteTCA X U y)) = f (TypeSubstitution.substituteTCA X U (PlutusIR.Ty_SOP (a0::l)))).
    {
      autorewrite with substituteTCA.
      simpl.
      auto.
    }
    rewrite H0.
             
        assert  (@fold_right STLC.term PlutusIR.ty
            (fun (T : PlutusIR.ty) (acc2 : STLC.term) =>
          @tmbin Fun (f T) acc2)
            (@fold_right STLC.term (list PlutusIR.ty)
            (fun (Ts : list PlutusIR.ty) (acc : STLC.term) =>
          @fold_right STLC.term PlutusIR.ty
            (fun (T : PlutusIR.ty) (acc2 : STLC.term) =>
          @tmbin Fun (f T) acc2)
            acc
            Ts)
            (tmbuiltin PlutusIR.DefaultUniInteger)
            l)
            a0
         = f ((PlutusIR.Ty_SOP (a0::l)))).
         {
            simpl. auto.
         }
         rewrite H2.
         eapply H; eauto.
         clear.
         simpl.
         lia.
  + (* tmbuiltin *)
    induction T; subst; inversion HeqfT; subst.
    * subst.
      autorewrite with substituteTCA.
      simpl. auto.
    * (* todo: inversion stuff, should be possible to automate, or at least to do that not in this function *)
      induction l; subst; inversion HeqfT.
      - autorewrite with substituteTCA. simpl. auto.
      - induction a; subst; inversion H2.
        
        assert (f
          (TypeSubstitution.substituteTCA X U
          (PlutusIR.Ty_SOP ([] :: l))) = f
          (TypeSubstitution.substituteTCA X U
          (PlutusIR.Ty_SOP (l)))).
        {
          autorewrite with substituteTCA.
          simpl.
          auto.
        }
        rewrite H0; clear H0.
        eapply IHl; intros; auto.
Qed.
        
Theorem f_preserves_step s s' :
  Type_reduction.step s s' -> step_nd (f s) (f s').
Proof.
  intros H.
  induction H; simpl; eauto; try solve [constructor; eauto].
  - rewrite f_preserves_substituteTCA.
    constructor.
  - induction f0; simpl.
    + induction f1; simpl; constructor; auto.
    + induction x; simpl; try constructor; auto.
      apply IHx.
      inversion f0; subst. auto.
Defined.

Theorem f_preserves_kind Δ s K :
  Kinding.has_kind Δ s K -> STLC_Kinding.has_kind Δ (f s) K.
Proof with subst; auto.
  intros.
  apply Checker.prop_to_type in H.
  induction H using Kinding.has_kind_set__ind.
  all: try solve [intros; try econstructor; eauto].
  simpl.
  induction Tss.
  - repeat constructor; induction IHhas_kind; auto.
  - simpl.
    induction a; auto.
    + eapply IHTss.
      inversion H; auto.
    + constructor.
      * inversion H; subst. inversion H2; auto.
      * apply IHa.
        constructor.
        -- inversion H.
              inversion H2; auto.
        -- inversion H; auto.
Qed.

(* Forward simulation *)
Lemma sn_preimage2 {e2 : PlutusIR.ty -> PlutusIR.ty -> Type} {e : STLC.term -> STLC.term -> Type} 
  (h : PlutusIR.ty -> STLC.term) (x : PlutusIR.ty) :
  (forall x y, e2 x y -> e (h x) (h y)) -> @sn STLC.term e (h x) -> @sn PlutusIR.ty e2 x.
Proof.
  intros A B.
  remember (h x) as v. (* this allows us to keep B : sn v as an hypothesis*)
  generalize dependent h.
  generalize dependent x.
  induction B.
  intros x0 h A eqn.
  apply SNI.
  intros y C.
  apply A in C.
  
  specialize (X (h y)).
  rewrite <- eqn in C.
  eapply X.
  - assumption.
  - exact A.
  - reflexivity.
Defined.

Theorem sn_step_nd_to_sn_step : forall s, @sn STLC.term step_nd (f s) -> @sn PlutusIR.ty Type_reduction.step s.
Proof.
  intros s.
  eapply @sn_preimage2 with (h := f) (e2 := Type_reduction.step) (e := step_nd).
  apply f_preserves_step.
Defined.

Corollary plutus_ty_strong_normalization s Δ K : Kinding.has_kind Δ s K -> @sn PlutusIR.ty Type_reduction.step s.
Proof.
  intros Hwk.
  apply f_preserves_kind in Hwk.
  apply strong_normalization_nd in Hwk.
  apply sn_step_nd_to_sn_step.
  auto.
Defined.