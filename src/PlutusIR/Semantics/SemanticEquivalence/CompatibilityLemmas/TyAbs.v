Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.BaseKindedness.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Require Import Arith.




Lemma compatibility_TyAbs: forall Delta Gamma bX K T e e',
    LR_logically_approximate ((bX, K) :: Delta) Gamma e e' T ->
    LR_logically_approximate Delta Gamma (TyAbs bX K e) (TyAbs bX K e') (Ty_Forall bX K T).
Proof with eauto_LR.
  (* intros Delta Gamma bX K T e e' IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH__e]].

  split... split...

  intros k rho env env' HRD HRG.

  autorewrite with RC.

  rewrite msubstA_TyAbs. rewrite msubstA_TyAbs.
  rewrite msubst_TyAbs. rewrite msubst_TyAbs.
  rewrite msubstT_TyForall. rewrite msubstT_TyForall.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.

  eexists. eexists.

  split. {
    eapply eval_result__result. apply R_TyAbs.
  }

  split... {
    apply T_TyAbs in Htyp__e.
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
    apply T_TyAbs in Htyp__e'.
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

  eexists. eexists.

  split... split...

  intros.
  rewrite substA_msubst by eauto using Ty.kindable_empty__closed.
  rewrite substA_msubst by eauto using Ty.kindable_empty__closed.
  rewrite <- substA_msubstA by eauto using Ty.kindable_empty__closed.
  rewrite <- substA_msubstA by eauto using Ty.kindable_empty__closed.

  eapply IH__e.
  - eapply RD_cons; eauto.
  - apply RG_extend_rho.
    eapply RG_monotone; eauto.
    rewrite <- minus_n_O in Hlt_i.
    apply Nat.lt_le_incl.
    assumption. *)
Admitted.
