Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Util.
Require Import PlutusCert.Util.Map.
Require Import PlutusCert.Util.Map.Mupdate.

Require Import Arith.
Require Import Coq.Lists.List.

Lemma compatibility_LetNonRec_nil : forall Delta Gamma t t' T,
    Delta |-* T : Kind_Base ->
    LR_logically_approximate Delta Gamma t t' T ->
    LR_logically_approximate Delta Gamma (Let NonRec nil t) (Let NonRec nil t') T.
Proof with eauto_LR.
  intros Delta Gamma t t' T Hkind__T IHLR__t.
  unfold LR_logically_approximate.

  destruct IHLR__t as [Htyp__t [Htyp__t' IH__t]].

  split... 
  split...

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  autorewrite with RC.

  rewrite msubstA_LetNonRec_nil. rewrite msubstA_LetNonRec_nil.
  rewrite msubst_LetNonRec_nil. rewrite msubst_LetNonRec_nil.

  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f. subst.
  inversion H3. subst.
  rename j0 into j_1.
  rename H3 into Hev'__e_f.
  rename H0 into Hev''__e_f.
  

  assert (HRC__t : RC k T rho 
    (msubst_term env (msubstA_term (msyn1 rho) t))
    (msubst_term env' (msubstA_term (msyn2 rho) t'))
  )...

  apply RC_to_RV with (j := j_1) (e_f := e_f) in HRC__t as temp...
  destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV__t]]].

  eexists. eexists.

  split. eapply E_Let. eapply E_Let_Nil...
  split. eapply RV_typable_empty_1...
  split. eapply RV_typable_empty_2...

  eapply RV_condition... 
  eapply RV_monotone...
Qed.