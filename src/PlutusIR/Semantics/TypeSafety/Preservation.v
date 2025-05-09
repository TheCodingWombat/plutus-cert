Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.
Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.UniqueTypes.
Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.

(* SubstituteT behaves as substituteTCA when substituting closed types *)
Lemma closed__substituteT_CA : 
  forall X U T,
    Ty.closed U ->
    substituteTCA X U T = substituteT X U T.
Proof.
Admitted.

Require Import Coq.Program.Equality.

(* Term language type preservation of closed terms under evaluation/reduction
   Per issue 83, errors are not preserved.
*)
Theorem eval__type_preservation : forall t T v k,
    nil ,, nil |-+ t : T ->
    t =[k]=> v ->
    (nil ,, nil |-+ v : T).
Proof.
    intros t T v k Ht Hbs.
    generalize dependent T.
    induction Hbs; intros.
    - (* E_LamAbs *)
      left.
      exact Ht.
    - (* E_Apply *)
      admit.
    - (* E_TyAbs *)
      
      left.
      exact Ht.
    - (* E_TyInst *)
      eapply IHHbs2.
      admit.
    - (* E_IWrap *)
      admit.
    - (* E_Unwrap *)
      admit.
    - (* E_Constant*)
      left.
      exact Ht.
    - (* E_Constr_nil *)
      left.
      exact Ht.
    - (* E_Constr_cons *)
      
      admit.
      (* TODO: No typing rules for constr?*)
    - (* E_Builtin *)
      left.
      exact Ht.
    - (* E_Apply_Builtin_Partial *)
      inversion Ht; subst.
      inversion H0; subst.
      + admit.
      + (* Hmm need some induction *)
        admit.
      + (* Some induction *)
        admit.
    - (* E_TyInst_Builtin_Partial *)
      admit.
    - (* E_Apply_Builtin_Full *)
      admit.
    - (* E_TyInst_Builtin_Full *)
      admit.
    - (* E_Error *)
      left.
      exact Ht.
    - (* E_Error_Apply1 *)

      (* Error rule was changed to allow
        type checking completeness to go through,
        but that does no longer work for 
        preservation now.

        Decided in meeting April 16 that we will keep it that way and 
        will not care about preservation of errors.
        *)
Admitted.