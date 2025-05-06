From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List AutosubstSsr.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import STLC_named STLC_named_typing ARS.
From PlutusCert Require Import alpha_typing alpha.alpha alpha_rename rename util alpha_ctx_sub freshness alpha_freshness.
From PlutusCert Require Import SN_STLC_named_naive gu_naive.pre gu_naive.constructions.

(* Define an infix operator for bind *)
Infix ">>=" := bind (at level 50, left associativity).



Inductive step_nd : term -> term -> Set :=
| step_beta_nd (x : string) (A : PlutusIR.kind) (s t : term) :
    step_nd (@tmapp App (@tmlam Lam x A s) t) (substituteTCA x t s) (* capture avoiding conservative substitutions *)
| step_appL_nd B s1 s2 t :
    step_nd s1 s2 -> step_nd (@tmapp B s1 t) (@tmapp B s2 t)
| step_appR_nd B s t1 t2 :
    step_nd t1 t2 -> step_nd (@tmapp B s t1) (@tmapp B s t2)
| step_abs_nd B x A s1 s2 :
    step_nd s1 s2 -> step_nd (@tmlam B x A s1) (@tmlam B x A s2).

Lemma in_ftv_existsb_true t s :
  In s (ftv t) -> existsb (eqb s) (ftv t) = true.
Proof.
  intros Hin.
  apply existsb_exists.
  exists s.
  split; auto.
  apply eqb_eq. auto.
Qed.

Lemma not_in_ftv_existsb_false t s :
  ~ In s (ftv t) <-> existsb (eqb s) (ftv t) = false.
Proof.
  split.
  - intros H.
    apply Bool.not_true_iff_false.
    intros He. apply existsb_exists in He.
    destruct He as [x [Hin Heqb] ].
    apply eqb_eq in Heqb. subst.
    contradiction.
  - intros H.
    intros Hcontra. apply in_ftv_existsb_true in Hcontra.
    rewrite H in Hcontra. discriminate.
Qed.


(* We need to change this to: GU s and no binder in s is free in t. Isnt that simply NC?*)
Lemma GU_substituteTCA_sub x t s : 
    NC s ((x, t)::nil) -> substituteTCA x t s = sub x t s.
Proof.
intros.
induction s; simpl.
- destr_eqb_eq x s.
  + autorewrite with substituteTCA. rewrite String.eqb_refl. reflexivity.
  + autorewrite with substituteTCA. rewrite <- String.eqb_neq in H0. rewrite H0. reflexivity.
- assert (x =? s = false).
  {
    apply nc_ftv_env with (x := s) in H. 
    - unfold ftv_keys_env in H. apply not_in_cons in H.  destruct H as [H _]. rewrite <- String.eqb_sym. 
      rewrite <- String.eqb_neq in H. assumption.
    - apply btv_lam.
  }
  autorewrite with substituteTCA.
  rewrite H0.
  assert (existsb (eqb s) (ftv t) = false).
  {
    apply nc_ftv_env with (x := s) in H. 
    - unfold ftv_keys_env in H. apply not_in_cons in H.  destruct H as [_ H]. apply not_in_app in H as [H _].
      apply not_in_ftv_existsb_false. assumption.
    - apply btv_lam.
  } 
  rewrite H1.
  f_equal.
  apply IHs.
  eapply nc_lam. eauto.
- autorewrite with substituteTCA. f_equal.
  + eapply IHs1; eapply nc_app_l. eauto.
  + eapply IHs2; eapply nc_app_r. eauto.
- autorewrite with substituteTCA. auto.
Qed.

(* If t has globally unique binders (and free variables to make it easier)
    then deterministic step and naive step coincide*)
Lemma GU_step_d_implies_step_na t t' : 
    GU t -> step_nd t t' -> step_naive t t'.
Proof.
    intros HGU_vars H.
    induction H.
    - (* we can be sure that no binder in s appears in t by global uniqueness*)
      assert (substituteTCA x t s = sub x t s) as Hsub.
      { 
          eapply GU_substituteTCA_sub.
          eapply gu_applam_to_nc. eauto.
        }
      rewrite Hsub.
      apply step_beta.
    - apply step_appL. auto. inversion HGU_vars; auto.
    - apply step_appR. auto. inversion HGU_vars; auto.
    - apply step_abs. auto. inversion HGU_vars; auto.
Qed.

Lemma subs_preserves_alpha' X T i : forall s s' R1 R2 R,
  R ⊢ (tmvar X) ~ (tmvar X) ->
  R ⊢ T ~ T ->
  αCtxTrans R1 R2 R ->
  R1 ⊢ s ~ i ->
  R2 ⊢ i ~ s' ->
  R ⊢ substituteTCA X T s ~ substituteTCA X T s'.
Proof.
  induction i as [xi | B xi ? bi | B i1 IHi1 i2 IHi2|d];
  intros s s' R1 R2 R Ha_X Ha_T Htrans Hαs Hαs';
    inversion Hαs as [xs ? ? Hαvs | xs ? ? bs ? ? Hαbs | s1 ? s2 ? ? Hαs1 Hαs2 |]; subst;
    inversion Hαs' as [? xs' ? Hαvs' |? xs' ? ? bs' ? Hαbs' | ? s1' ? s2' ? Hαs1' Hαs2'|]; 
    subst; simpl.
  - (* Case: tmvar *)
    repeat rewrite substituteTCA_equation_1.
    assert (Hαv: AlphaVar R xs xs'). { eapply alpha_var_trans; eauto. }
    destr_eqb_eq X xs.
    + inversion Ha_X; subst.
      apply (alphavar_unique_right H2) in Hαv. subst. rewrite String.eqb_refl. 
      assumption.
    + inversion Ha_X; subst.
      remember (Hαv) as Hαv'. clear HeqHαv'.
      apply (alphavar_unique_not_left H H3) in Hαv.
      rewrite <- String.eqb_neq in Hαv.
      rewrite Hαv. 
      constructor.
      auto.
  - (* Case: tmlam *)
    
    (* remember (fresh2 _ bs) as b; rewrite cons_to_append in Heqb.
    remember (fresh2 _ bs') as b'; rewrite cons_to_append in Heqb'. *)
    (* idk, but it is true.*)
    destr_eqb_eq x X.
    + rewrite substituteTCA_equation_2.
      remember (fresh2 _ s1) as b; rewrite cons_to_append in Heqb.
      rewrite String.eqb_refl.
      eapply @alpha_sym with (ren := sym_alpha_ctx R); eauto with α_eq_db.
      eapply substituteTCA_vacuous; eauto with α_eq_db.
      eapply @alpha_preserves_no_ftv with (x := X) (s := tmlam X k s1).
      * apply ftv_lam_no_binder.
      * eauto with α_eq_db.
      * inversion Ha_X; eauto.
    + destr_eqb_eq y X.
      * assert (Hvac_sub: substituteTCA X T (@tmlam B X k s2) = @tmlam B X k s2).
        {
          rewrite substituteTCA_equation_2.
          rewrite String.eqb_refl.
          reflexivity.
        }
        rewrite Hvac_sub.
        eapply substituteTCA_vacuous; eauto with α_eq_db.
        eapply @alpha_preserves_no_ftv with (x := X) (s := tmlam X k s2).
        -- apply ftv_lam_no_binder.
        -- eauto with α_eq_db.
        -- inversion Ha_X; eauto. eapply @alphavar_sym with (ren := R); eauto with α_eq_db.
      * autorewrite with substituteTCA.
        rewrite <- String.eqb_neq in H1. rewrite String.eqb_sym in H1. rewrite H1.
        rewrite <- String.eqb_neq in H2. rewrite String.eqb_sym in H2. rewrite H2.

        destruct (existsb (eqb x) (ftv T)) eqn:Hin; destruct (existsb (eqb y) (ftv T)) eqn:Hin'.
        -- simpl.
           remember (fresh2 _ s1) as Y'.
           remember (fresh2 _ s2) as Y''.
           constructor.
           eapply IHbi; eauto.
           ++ eapply alpha_extend_fresh; auto.
              ** eapply fresh2_over_key_sigma with (X := X) in HeqY'.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_eq.
              ** eapply fresh2_over_key_sigma with (X := X) in HeqY''.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_eq.
           ++ eapply alpha_extend_fresh; auto.
              ** eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY'.
                 intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
                 apply in_eq.
              ** eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY''.
                 intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
                 apply in_eq.
           ++ constructor; eauto.
           ++ eapply alpha_trans_rename_left; eauto.
           ++ eapply alpha_trans_rename_right; eauto.
        -- simpl.
           remember (fresh2 _ s1) as Y'.
           constructor.
            eapply IHbi; eauto.
            ++ eapply alpha_extend_fresh; auto.
              ** eapply fresh2_over_key_sigma with (X := X) in HeqY'.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_eq.
              ** intros Hcontra. apply ftv_var in Hcontra. subst.
                 rewrite String.eqb_neq in H2. contradiction.
            ++ eapply alpha_extend_fresh; auto.
              ** eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY'.
                 intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
                 apply in_eq.
              ** eapply not_in_ftv_existsb_false. auto.
            ++ eauto with α_eq_db.
            ++ eapply alpha_trans_rename_left; eauto.
        -- simpl.
           remember (fresh2 _ s2) as Y'.
           constructor.
           eapply IHbi; eauto. 
           ++ eapply alpha_extend_fresh; auto.
              ** intros Hcontra. apply ftv_var in Hcontra; subst.
                  rewrite String.eqb_neq in H1. contradiction.
              **  
                eapply fresh2_over_key_sigma with (X := X) in HeqY'.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_eq.

           ++ eapply alpha_extend_fresh; auto.
              eapply not_in_ftv_existsb_false. auto.
              eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY'.
              intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
              apply in_eq.
           ++ constructor; eauto.
           ++ eapply alpha_trans_rename_right; eauto.
        -- constructor; eapply IHbi; eauto.
           ++ apply alpha_extend_fresh; auto.
              ** intros Hcontra. apply ftv_var in Hcontra; subst.
                  rewrite String.eqb_neq in H1. contradiction.
              ** intros Hcontra. apply ftv_var in Hcontra; subst.
                  rewrite String.eqb_neq in H2. contradiction.
           ++ eapply alpha_extend_fresh; auto.
              eapply not_in_ftv_existsb_false. auto.
              eapply not_in_ftv_existsb_false. auto.
           ++ eauto with α_eq_db.  
  - autorewrite with substituteTCA.
    constructor.
    + eapply IHi1; eauto.
    + eapply IHi2; eauto.
  - autorewrite with substituteTCA.
    constructor.
Qed.

Lemma substituteTCA_preserves_alpha s s' ren X U:
  ren ⊢ (tmvar X) ~ (tmvar X) ->
  (ren ⊢ U ~ U) ->
  (ren ⊢ s ~ s') ->
  Alpha ren (substituteTCA X U s) (substituteTCA X U s').
Proof.
  intros.
  apply (@subs_preserves_alpha' X U s s s' (nil ++ ctx_id_left ren) ren ren); auto.
  - apply id_left_trans; auto.
  - apply alpha_extend_ids_right.
    + apply ctx_id_left_is_id.
    + apply alpha_refl. apply alpha_refl_nil.
Qed.

Lemma alpha_capms_to_naive X U T:
  {T' & Alpha [] T T' * Alpha [] (substituteTCA X U T) (sub X U T') * NC T' ((X, U)::nil)}%type.
Proof.
  exists (to_GU' X U T).
  split; [split|].
  - apply to_GU'__alpha.
  - eapply @alpha_trans with (t := substituteTCA X U (to_GU' X U T)).
    constructor.
    + eapply substituteTCA_preserves_alpha. eapply alpha_refl. constructor. eapply alpha_refl. constructor. apply to_GU'__alpha.
    + erewrite GU_substituteTCA_sub.
      * apply alpha_refl. constructor.
      * apply to_GU'__NC.
  - apply to_GU'__NC.
Qed.

(* Main lemma for going from using t alpha t' in SN t' to SN t*)
Lemma step_nd_preserves_alpha ren s t s' :
  Alpha ren s t -> step_nd s s' -> {t' & (step_nd t t') * (Alpha ren s' t')}%type.
Proof.
  intros Halpha Hstep.
  generalize dependent t.
  generalize dependent ren.
  induction Hstep; intros ren t0 Halpha; inversion Halpha; subst.
  - inversion H4; subst.
    remember (alpha_capms_to_naive x t s).
    destruct s1 as [s' [ [Halpha1 Halpha2] Halpha3] ].
    eexists.
    split.
    + apply step_beta_nd.
    + eapply @alpha_trans with (t := sub x t s').
      * apply id_left_trans.
      * change (ctx_id_left ren) with (nil ++ ctx_id_left ren).
        apply alpha_extend_ids_right.
        -- apply ctx_id_left_is_id.
        -- auto.
      * remember (alpha_capms_to_naive y t2 s0).
        destruct s1 as [t' [ [Halpha1' Halpha2'] Halpha3' ] ].
      
        eapply @alpha_trans with (t := sub y t2 t').
        -- apply id_right_trans.
        -- eapply alpha_rename_binder_stronger with (Rs := ((x, y)::ren)); eauto.
           ++ eapply @alpha_trans with (t := s) (ren := ctx_id_left ((x, y)::ren)) (ren' := ((x, y)::ren)); eauto with α_eq_db.
              ** apply id_left_trans.
              ** apply alpha_extend_ids.
                 --- apply ctx_id_left_is_id.
                 --- eapply alpha_sym. constructor. eauto.
              ** eapply @alpha_trans with (t := s0) (ren := ((x, y)::ren)) (ren' := ctx_id_right ((x, y)::ren)); eauto with α_eq_db.
                  --- apply id_right_trans.
                  --- apply alpha_extend_ids.
                      +++ apply ctx_id_right_is_id.
                      +++ eapply alpha_sym. constructor. eauto with α_eq_db.
           ++ constructor.
        -- change (ctx_id_right ren) with (nil ++ ctx_id_right ren).
           apply alpha_extend_ids_right.
           ++ apply ctx_id_right_is_id.
           ++ eapply alpha_sym. constructor. eauto.
  - destruct (IHHstep ren s3 H4) as [t1_α [Hstep' Halpha'] ].
    exists (@tmapp B t1_α t2); split.
    + apply step_appL_nd. assumption.
    + apply alpha_app; assumption.
  - destruct (IHHstep ren t4 H5) as [tα [Hstep' Halpha'] ].
    exists (@tmapp B s2 tα); split.
    + apply step_appR_nd; auto.
    + apply alpha_app; assumption.
  - destruct (IHHstep ((x, y)::ren) s3 H5) as [tα [Hstep' Halpha'] ].
    exists (@tmlam B y A tα); split.
    + apply step_abs_nd. assumption.
    + apply alpha_lam; assumption.    
Qed.

Lemma step_nd_implies_step_gu_na t t' : 
    step_nd t t' ->  
    {t_α & step_gu t t_α * (nil ⊢ t' ~ t_α)}%type.
Proof with auto using to_GU__alpha, to_GU__GU.
    intros.
    destruct (step_nd_preserves_alpha (to_GU__alpha t) H) as [t_GU' [Hstep_GU Halpha_GU] ].
    exists t_GU'; split; auto.
    apply GU_step_d_implies_step_na in Hstep_GU...
    apply step_gu_intro with (s' := (to_GU t))...
Qed.

Theorem α_preserves_sn_nd s s' :
  Alpha [] s s' -> (@sn term step_nd) s -> (@sn term step_nd) s'.
Proof.
  intros Hα Hsn.
  generalize dependent s'.
  induction Hsn. intros s' Hα.
  apply SNI.
  intros y1 Hstep.
  assert ({y1_α & prod (step_nd x y1_α) (nil ⊢ y1 ~ y1_α)}) as [y1_α [Hstep' Hα'] ].
  {
    eapply step_nd_preserves_alpha; auto.
    - eapply alpha_sym in Hα. exact Hα. apply alpha_sym_nil.
    - assumption.
  }
  eapply X.
  - exact Hstep'.
  - eapply alpha_sym. apply alpha_sym_nil. exact Hα'.
Qed.

Lemma SN_na_to_SN_nd t : (@sn term step_gu) t -> (@sn term step_nd) t.
Proof.
  intros Hsn_nd.
  apply SNI.
  intros t' Hstep.
  generalize dependent t'.
  induction Hsn_nd; intros t Hstep_d.
  assert (Hstep_alpha: {t' & prod (step_gu x t') (Alpha nil t t')}).
  {
    eapply step_nd_implies_step_gu_na; eauto.
  }
  destruct Hstep_alpha as [t' [Hstep Halpha] ].
  specialize (X t' Hstep).
  apply α_preserves_sn_nd with t'.
  - eapply alpha_sym; [apply alpha_sym_nil |].
    assumption.
  - apply SNI. 
    exact X.
Qed.

Theorem strong_normalization E s T : STLC_named_typing.has_kind E s T -> (@sn term step_nd) s.
  intros.
  apply SN_naive in H. 
  apply SN_na_to_SN_nd.
  assumption.
Qed.