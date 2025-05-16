Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
From PlutusCert Require Import Analysis.BoundVars.
From PlutusCert Require Import Analysis.FreeVars.

Require Export PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.Normalisation.Normalisation.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.PlutusIR.Semantics.Static.Builtins.Signatures.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Export PlutusCert.PlutusIR.Analysis.FreeVars.
Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.
From PlutusCert Require Import util.


Import Coq.Lists.List.
Import ListNotations.
Import Coq.Strings.String.
Local Open Scope string_scope.

Definition K_id : kind := Kind_Arrow (Kind_Base) (Kind_Base).
Definition Tint : ty := Ty_Builtin DefaultUniInteger.
Definition id_type : ty := Ty_Lam "β" Kind_Base (Ty_Var "β").

Definition t : term := TyInst
    (TyAbs "α" (K_id) 
        (LamAbs "x" (Ty_App (Ty_Var "α") Tint) (Var "x")))
    id_type. 

Lemma t_well_kinded :
     [] ,, [] |-+ t : (Ty_Fun Tint Tint).
Proof.
    unfold Tint. unfold t.
    unfold K_id.
    unfold id_type.
    unfold K_id.
    eapply T_TyInst with (X := "α") (K2 := K_id) (T1n := Ty_Fun (Ty_App (Ty_Var "α") Tint) (Ty_App (Ty_Var "α") Tint)).
    - apply T_TyAbs.
      simpl.
      unfold drop_ty_var. simpl.
      apply T_LamAbs.
      + econstructor. econstructor. simpl. unfold K_id. f_equal. unfold Tint. repeat constructor.
      + apply N_TyApp; repeat econstructor.
      + eapply T_Var; eauto. simpl; eauto. repeat econstructor.
        apply N_TyApp; repeat econstructor.
    - repeat econstructor.
    - apply N_TyLam. constructor.
    - unfold Tint.
      autorewrite with substituteTCA.
      repeat constructor.
      + rewrite String.eqb_refl.
        repeat econstructor.
        autorewrite with substituteTCA.
        rewrite String.eqb_refl.
        repeat constructor.
      + rewrite String.eqb_refl.
        repeat econstructor.
        autorewrite with substituteTCA.
        rewrite String.eqb_refl.
        repeat constructor.
Qed.
