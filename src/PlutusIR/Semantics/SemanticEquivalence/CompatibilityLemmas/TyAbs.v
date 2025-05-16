Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.BaseKindedness.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

From PlutusCert Require Import FreeVars.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Require Import Arith.

Search "RC".

(* TODO: Not sure if this holds *)
Lemma RC_rename_T k T rhos ρ e e' bX bY :
    ~ In bY (Ty.ftv T) ->
    ~ In bY (Ty.btv T) ->
    RC k T                                ((bX, ρ)::rhos) e e' ->
    RC k (substituteT bX (Ty_Var bY) T) ((bY, ρ)::rhos) e e'.
Proof.
  intros Hftv Hbtv HRC.
  generalize dependent rhos.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent k.
  induction T; intros.
  - (* Ty_Var *)
    simpl.
    destruct (String.eqb bX t) eqn:Heqb.
    + assert (t = bX). { apply String.eqb_eq in Heqb. auto. } subst.
      autorewrite with RC in HRC.
      autorewrite with RC; intros.
      specialize (HRC _ Hlt_j _ H).
      destruct HRC as [e'_f [j' HRC]].
      exists e'_f.
      exists j'.
      destruct HRC as [HRC1 [HRC2 HRC3]].
      split; auto.
      split.
      * (* ADMIT: We know that bY gets substituted with the same type as bX will. through HRC2. *)
        admit.
      * destruct HRC3 as [HRC3_1 HRC3_2].
        split; auto.
        -- (* ADMIT: We know that bY gets substituted with the same type as bX will. through HRC3_1.*)
           admit.
        -- destruct HRC3_2 as [HRC3_2 | HRC3_2_error]; auto.
           left.
           destruct HRC3_2 as [HRC3_2_1 [HRC3_2_2 HRC3_2]].
           split; auto.
           split; auto.
           intros.
           apply HRC3_2.
           simpl. destruct ρ. destruct p.
           rewrite String.eqb_refl.
           simpl in H0.
           rewrite String.eqb_refl in H0.
           inversion H0; subst.
           auto.
    + assert (bY <> t).
      {(* By Hftv *)
         admit.
      }
      assert (HbXt: bX <> t) by admit.
            autorewrite with RC in HRC.
      autorewrite with RC; intros.
      specialize (HRC _ Hlt_j _ H0).
      destruct HRC as [e'_f [j' HRC]].
      exists e'_f.
      exists j'.
      destruct HRC as [HRC1 [HRC2 HRC3]].
      split; auto.
      split.
      * 
        simpl msyn1 in HRC2.
        destruct ρ.
        destruct p.
        simpl msubstT in HRC2.
        rewrite Heqb in HRC2.
        simpl msyn1.
        simpl msubstT.
        rewrite <- String.eqb_neq in H.
        rewrite H.
        assumption.
      * destruct HRC3 as [HRC3_1 HRC3_2].
        split; auto.
        -- (* ADMIT: see above: msyn2 skips over (bX, ρ) and (bY, ρ) because of inequality to t.
            Then by assumption. *)
            admit.
        -- destruct HRC3_2 as [HRC3_2 | HRC3_2_error]; auto.
           left.
           destruct HRC3_2 as [HRC3_2_1 [HRC3_2_2 HRC3_2]].
           split; auto.
           split; auto.
           intros.
           apply HRC3_2.
           simpl. destruct ρ. destruct p.
           rewrite String.eqb_sym in Heqb.
           rewrite Heqb.
           simpl in H1.
           rewrite <- String.eqb_neq in H.
           rewrite String.eqb_sym in H.
           rewrite H in H1.
           rewrite H1.
           auto.
  - admit.
  - admit.
  - (* Ty_Forall *)
    simpl.
    assert (Hby_b: bY <> b) by admit. (* by Hbtv*)
    assert (Hftv_T: ~ In bY (Ty.ftv T)) by admit. (* by Hftv and Hbtv *)
    assert (Hbtv_T: ~ In bY (Ty.btv T)) by admit. (* by Hbtv *)
    specialize (IHT Hftv_T Hbtv_T).

    destruct (String.eqb bX b) eqn:Heqb.
    + clear IHT.
      (* bX = b 
       
        but when RC'ing body of forall in HRC, b will shadow bX
          probably some shadowign thing

        bY does not occur in T, so we can remove it/ it is unused, just like bX above.
         then when RCing body, also b comes in front. Hence by HRC and some weakening argument?

      *)admit.
    + (* bx <> b *)
      (* by some swap rhos argument/weakening, we can instantiate IHT 
        with rhos := (b, something)::(bY, rho) :: rhos*)

        (* Then again we can prove IHT assumption by
          swap rhos.
          *)
      autorewrite with RC in HRC.
      autorewrite with RC; intros.
      specialize (HRC _ Hlt_j _ H).
      destruct HRC as [e'_f [j' HRC]].
      eexists. eexists.
      destruct HRC as [HRC1 [HRC2 HRC3]].
      split; eauto.
      destruct HRC2 as [HRC2_1 HRC2_2].
      split.
      { 
        (* ADMIT: subst bX for bY, but then subst bY for rho,
            and hypothesis substs bX for rho immediately. Should be the same by bY fresh.
        *)  
        admit. 
      }
      destruct HRC3 as [HRC3_1 HRC3_2].
      split. { 
        (* ADMIT: See above *)  
        admit. 
      }
      destruct HRC3_2 as [HRC3_2 | HRC3_2_error]; auto.
      left.
      destruct HRC3_2 as [HRC3_2_1 [HRC3_2_2 HRC3_2]].
      split; auto.
      split; auto.
      destruct HRC3_2 as [e_body [e'_body [Y [ Z [He_f [He'_f HRC3_2]]]]]].
      exists e_body. exists e'_body. exists Y. exists Z.
      split; auto.
      split; auto.
      intros.
      specialize (HRC3_2 T1 T2 Chi H0 H1 H2 i Hlt_i).

      (* NOT TRUE, but allowed by weakening *)
      assert (HswapbY: ( ((b, (Chi, T1, T2)) :: (bY, ρ) :: rhos)) =  ((bY, ρ) :: (b, (Chi, T1, T2)) :: rhos)).
      {
        admit.
      }
      rewrite HswapbY.
      eapply IHT.
      assert (HswapbX: ( ((b, (Chi, T1, T2)) :: (bX, ρ) :: rhos)) =  ((bX, ρ) :: (b, (Chi, T1, T2)) :: rhos)).
      {
         (* Not true again, but allowed by weakening and b <> bX*)
        admit.
      }
      rewrite <- HswapbX.
      assumption.
  - (* Ty_Builtin *)
    autorewrite with RC.
    autorewrite with RC in HRC.
    intros.
    specialize (HRC _ Hlt_j _ H).
    destruct HRC as [e'_f [j' HRC]].
    exists e'_f.
    exists j'.
    destruct HRC as [HRC1 [HRC2 HRC3]].
    split; auto.
    split; auto.
    + (* ADMIT: Substitution on builtins doesnt do anything *)
      admit.
    + destruct HRC3 as [HRC3_1 HRC3_2].
      split; auto.
      (* ADMIT: Substitution on builtins doesnt do anything *)
      admit.
  - (* Ty_Lam *)
    
    autorewrite with RC.
    autorewrite with RC in HRC.
    intros.
    specialize (HRC _ Hlt_j _ H).
    destruct HRC as [e'_f [j' HRC]].
    exists e'_f.
    exists j'.
    destruct HRC as [HRC1 [HRC2 HRC3]].
    split; auto.
    split; auto.
    + destruct (String.eqb bX b) eqn:Heqb.
      * assert (bX = b) by admit.
        subst. simpl. destruct ρ. destruct p.
        rewrite String.eqb_refl.
        (* ADMIT: bY is not in Ty_Lam b k0 T, so we can remove the substitution 
          Then by HRC2 (there we can also remove the substitution b)
          *)
        admit.
      * simpl.
        destruct ρ. destruct p.
        rewrite Heqb.
        (* ADMIT: lambda binder is not equal to bX or bY, should hold by inductive argument thruogh HRC*)
        admit.
    + destruct HRC3 as [HRC3_1 HRC3_2].
      split; auto.
      -- (* ADMIT: Same reasoning as above *)
         admit.
      -- destruct HRC3_2 as [HRC3_2 | HRC3_2_error]; auto.
         destruct HRC3_2 as [HRC3_2_1 [HRC3_2_2 HRC3_2]]; contradiction.
  - (* Ty_App *)
    autorewrite with RC.
    autorewrite with RC in HRC.
    intros.
    specialize (HRC _ Hlt_j _ H).
    destruct HRC as [e'_f [j' HRC]].
    exists e'_f.
    exists j'.
    destruct HRC as [HRC1 [HRC2 HRC3]].
    split; auto.
    split; auto.
    + admit.
    + destruct HRC3 as [HRC3_1 HRC3_2].
      split; auto.
      (* ADMIT: Same reasoning as above *)
      admit.
Admitted.

Require Import Coq.Lists.List.

Lemma compatibility_TyAbs: forall Delta Gamma bX bY K T e e',
    LR_logically_approximate ((bX, K) :: Delta) (drop_ty_var bX (drop_ty_var bY Gamma)) e e' T ->
    ~ In bY (Ty.ftv T) ->
    ~ In bY (Ty.btv T) ->
        LR_logically_approximate Delta Gamma (TyAbs bX K e) (TyAbs bX K e') 
                (Ty_Forall bY K (substituteT bX (Ty_Var bY) T)).
Proof with eauto_LR.
  intros Delta Gamma bX bY K T e e' IH_LR Hftv Hbtv.
  unfold LR_logically_approximate.
  
  destruct IH_LR as [Htyp__e [Htyp__e' IH__e]].

  split... 
  split...

  intros k rho env env' HRD HRG.

  autorewrite with RC.

  rewrite msubstA_TyAbs. rewrite msubstA_TyAbs.
  rewrite msubst_TyAbs. rewrite msubst_TyAbs.
  rewrite msubstT_TyForall. rewrite msubstT_TyForall.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.

  eexists. eexists.

  split. {
    eapply eval_result. apply R_Value. apply V_TyAbs.
  }

  split... 
  (* BROKEN BY new tyabs rule! *)
  {
    apply T_TyAbs in Htyp__e; auto.
    eapply has_type__basekinded in Htyp__e as H...
    eapply closing_preserves_kinding_1 in H as H0...
    rewrite msubstT_TyForall in H0.
    apply strong_normalisation in H0 as H1.
    destruct H1.
    inversion H1. subst.
    eexists. split...
    eapply closingA_preserves_typing_1 in Htyp__e...
    2: {
      rewrite msubstT_TyForall...
    }
    eapply closing_preserves_typing_1 in Htyp__e...
    rewrite msubstA_TyAbs in Htyp__e.
    rewrite msubst_TyAbs in Htyp__e.
    eauto.
  }
  split... {
    apply T_TyAbs in Htyp__e'; auto.
    eapply has_type__basekinded in Htyp__e' as H...
    eapply closing_preserves_kinding_2 in H as H0...
    rewrite msubstT_TyForall in H0.
    apply strong_normalisation in H0 as H1.
    destruct H1.
    inversion H1. subst.
    eexists. split...
    eapply closingA_preserves_typing_2 in Htyp__e'...
    2: {
      rewrite msubstT_TyForall...
    }
    eapply closing_preserves_typing_2 in Htyp__e'...
    rewrite msubstA_TyAbs in Htyp__e'.
    rewrite msubst_TyAbs in Htyp__e'.
    eauto.
  }

  left. split. intros Hcon. inversion Hcon. split. intros Hcon. inversion Hcon.

  eexists. eexists. eexists. eexists.

  split... split...

  intros.
  rewrite substA_msubst by eauto using Ty.kindable_empty__closed.
  rewrite substA_msubst by eauto using Ty.kindable_empty__closed.
  rewrite <- substA_msubstA by eauto using Ty.kindable_empty__closed.
  rewrite <- substA_msubstA by eauto using Ty.kindable_empty__closed.

  assert (close env (msyn1 rho) (substA bX T1 e) 
    = close env (msyn1 ((bX, (Chi, T1, T2))::rho)) e) by auto.
  assert (close env' (msyn2 rho) (substA bX T2 e') = 
    close env' (msyn2 ((bX, (Chi, T1, T2))::rho)) e') by auto.
  rewrite H2.
  rewrite H3.
  (* ADMIT: bX vs bY. T is related to e/e' with bX*)

  assert (RC i T ((bX, (Chi, T1, T2))::rho) (close env (msyn1 ((bX, (Chi, T1, T2))::rho)) e)
    (close env' (msyn2 ((bX, (Chi, T1, T2))::rho)) e')).
  {
    eapply IH__e.
    - eapply RD_cons; eauto.
    - apply RG_extend_rho.
      eapply RG_monotone; eauto.
      (*
      ADMIT: I think same as TyAbs issue 16 branch, see for solution after
        having merged PR80
             
      rewrite <- minus_n_O in Hlt__j.
      apply Nat.lt_le_incl.
      assumption. *)
      admit.
  }

  apply RC_rename_T; assumption.  

Admitted.