Require Import PlutusCert.PlutusIR.

Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.

Theorem unique_kinds_uni : forall d K K',
    |-*_uni d : K -> |-*_uni d : K' -> K = K'.
Proof.
  intros d K K' Hkind1.
  generalize dependent K'.
  induction Hkind1; intros K' Hkind2; inversion Hkind2; try reflexivity.
  - (* DefaultUni_App*) 
    subst.
    apply IHHkind1_2 in H3.
    subst.
    apply IHHkind1_1 in H1.
    inversion H1.
    reflexivity.
Qed.

Theorem unique_kinds : forall ctx T K K',
    ctx |-* T : K ->
    ctx |-* T : K' ->
    K = K'.
Proof.
  intros ctx T K K' Hkind1.
  generalize dependent K'.
  induction Hkind1; intros K' Hkind2; inversion Hkind2; subst; try reflexivity.
  - (* K_Var *)
    rewrite H in H2.
    inversion H2. subst.
    reflexivity.
  - (* K_Builtin *)
    apply unique_kinds_uni with (d := T); assumption.
  - (* K_Lam *)
    f_equal.
    apply IHHkind1.
    assumption.
  - (* K_App *)
    apply IHHkind1_2 in H4.
    subst.
    apply IHHkind1_1 in H2.
    inversion H2.
    subst.
    reflexivity.
Qed.
