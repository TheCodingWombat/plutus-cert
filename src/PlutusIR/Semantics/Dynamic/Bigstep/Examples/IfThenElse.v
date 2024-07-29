Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.


Ltac invert_neutrals :=
  match goal with
  | H : neutral_value ?n ?t |- False =>
      inversion H; clear H; subst; try invert_neutrals
  | H : neutral ?t |- False =>
      inversion H; clear H; subst; try invert_neutrals
  end.

Ltac decide_neutral :=
  match goal with
  | |- neutral ?nv =>
      unfold neutral; econstructor; simpl; eauto; try decide_neutral
  | |- neutral_value ?n ?nv =>
      econstructor; simpl; eauto; try decide_neutral
  | |- ?f <> ?f' =>
      let Hcon := fresh "Hcon" in
      try solve [intros Hcon; inversion Hcon]
  | |- ~ neutral ?t =>
      let Hcon := fresh "Hcon" in
      try solve [intros Hcon; invert_neutrals]
  | |- ~ is_error ?t =>
      let Hcon := fresh "Hcon" in
      try solve [intros Hcon; inversion Hcon]
  end.

Definition Ty_int : ty := Ty_Builtin DefaultUniInteger.
Definition int_and_int_to_int : ty := Ty_Fun Ty_int (Ty_Fun Ty_int Ty_int).

Example test_ifThenElse : forall x y, exists k,
  Apply (LamAbs x int_and_int_to_int (Apply (Apply (Var x) (constInt 17)) (constInt 3))) (Apply (TyInst (Apply (LamAbs y Ty_int (Builtin IfThenElse)) (constInt 666)) (Ty_Builtin DefaultUniInteger)) (Constant (ValueOf DefaultUniBool true))) =[k]=> constInt 17.
Proof with (eauto with hintdb__eval_no_error || (try solve [decide_neutral])).
  unfold constInt.
  intros.
  eexists.
  eapply E_Apply...
  - eapply E_NeutralApplyPartial...
    + eapply E_NeutralTyInstPartial...
      * eapply E_Apply...
      * simpl...
      * eapply E_NeutralTyInst...
    + simpl...
    + eapply E_NeutralApply...
  - simpl...
  - simpl. rewrite eqb_refl.
    eapply E_NeutralApplyFull...
    repeat econstructor...
Qed.
