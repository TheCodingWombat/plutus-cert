Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.

Ltac solver := try solve [repeat (econstructor; eauto)].

Require Import Coq.Lists.List.

(* Stronger than Kinding.weakening:
  x := freshUnwrapIFix F may shadow something in Δ
   when it is not used, because Δ may contain vars
   that are not free in F.
*)
Lemma weaken_fresh Δ F K K1 :
  Δ |-* F : K -> ((freshUnwrapIFix F, K1)::Δ) |-* F : K.
Admitted.

Lemma unwrapIFix__well_kinded F K T Δ :
  Δ |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
  Δ |-* T : K ->
  Δ |-* (unwrapIFix F K T) : Kind_Base.
Proof.
  intros.
  eapply K_App with (K1 := K); auto.
  eapply K_App with (K1 := Kind_Arrow K Kind_Base); auto.
  eapply K_Lam.
  eapply K_IFix with (K := K); auto.
  - remember (freshUnwrapIFix F) as X.
    constructor.
    simpl.
    rewrite String.eqb_refl.
    reflexivity.
  - apply weaken_fresh.
    assumption.
Qed.

Lemma uniType__basekinded : forall t A,
  uniType_option t = Some A ->
  |-*_uni t : Kind_Base
.
(* TODO: should hold, property of uniType_option *)
Admitted.

Lemma lookupBuiltinTy__well_kinded f Δ :
  Δ |-* (lookupBuiltinTy f) : Kind_Base.
Proof.
  destruct f; repeat constructor.
Qed.

Lemma has_type__basekinded : forall Delta Gamma t T,
    Delta ,, Gamma |-+ t : T ->
    Delta |-* T : Kind_Base.
Proof with (eauto || solver).
  induction 1; intros...
  all: try solve [econstructor; eauto using preservation]...
  all: try solve [eauto using preservation]...
  - (* T_LamAbs *) inversion IHhas_type1...
  - (* T_TyAbs *)
    constructor...
    (* ADMIT: Rename fresh preserves kinding? *)
    admit.
  - (* T_TyInst *) 
    inversion IHhas_type. subst.
    eapply preservation.
    2:{
      apply H2.
    }
    eapply substituteTCA_preserves_kinding...
    eapply preservation...
  - (* T_Unwrap *)
    unfold unwrapIFix in H1.
    inversion IHhas_type. subst.
    assert (K = K0).
    {
      eapply unique_kinds in H5; eauto.
    }
    subst.
    eapply preservation in H1; eauto.
    econstructor...
    econstructor...
    econstructor...
    econstructor...
    + econstructor...
      simpl.
      rewrite String.eqb_refl.
      eauto.
    + apply weaken_fresh.
      assumption.
  - (* T_Constant *)
    constructor...

    (* TODO: keep typing derivation around during induction and use uniType__basekinded *)
    admit.
  - (* T_Builtin*)
    subst.
    eapply preservation.
    apply lookupBuiltinTy__well_kinded.
    eauto.
  - (* T_LetNonRec *)
    admit.
  - (* T_LetRec *)
    admit.

(* ADMIT: This should hold if all types in gamma are base kinded, which should
   be the case since we only but base-kinded types in Gamma in our
   type rules. Needs some additional assumptions for the proof to go through. *)
Admitted.
