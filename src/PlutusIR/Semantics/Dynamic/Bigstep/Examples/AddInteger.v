Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.



Definition Ty_int : ty := Ty_Builtin DefaultUniInteger.
Definition int_to_int : ty := Ty_Fun Ty_int Ty_int.

Example test_addInteger : forall x, exists k,
  Apply (LamAbs x int_to_int (Apply (Var x) (constInt 17))) (Apply (Builtin AddInteger) (constInt 3))
  =[k]=> constInt 20.
Proof with (autounfold; eauto with hintdb__eval_no_error || (try solve [intros Hcon; inversion Hcon])).
  unfold constInt.
  intros.
  eexists.
  eapply E_Apply...
  - eapply E_NeutralApply...
    eapply NV_Apply...
  - intros Hcon.
    inversion Hcon.
  - simpl.
    rewrite eqb_refl.
    eapply E_NeutralApplyFull...
    eapply FA_Apply...
    eapply FA_Apply...
Qed.
