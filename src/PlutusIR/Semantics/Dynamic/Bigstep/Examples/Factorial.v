Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Definition fact_term (n : Z) : term :=
  Let
    Rec
    [ TermBind
        Strict
        (VarDecl
          "fact"
          (Ty_Fun
            (Ty_Builtin DefaultUniInteger)
            (Ty_Builtin DefaultUniInteger)
          )
        )
        (LamAbs
          "x"
          (Ty_Builtin DefaultUniInteger)
          (Apply
            (Apply
              (Apply
                (TyInst
                  (Builtin IfThenElse)
                  (Ty_Builtin DefaultUniInteger)
                )
                (Apply
                  (Apply
                    (Builtin EqualsInteger)
                    (Var "x")
                  )
                  (Constant (ValueOf DefaultUniInteger 0))
                )
              )
              (Constant (ValueOf DefaultUniInteger 1))
            )
            (Apply
              (Apply
                (Builtin MultiplyInteger)
                (Var "x")
              )
              (Apply
                (Var "fact")
                (Apply
                  (Apply
                    (Builtin SubtractInteger)
                    (Var "x")
                  )
                  (Constant (ValueOf DefaultUniInteger 1))
                )
              )
            )
          )
        )
    ]
    (Apply
      (Var "fact")
      (Constant (ValueOf DefaultUniInteger n))
    ).

Ltac invert_contra := let Hcon := fresh "Hcon" in intros Hcon; inversion Hcon.
Ltac destruct_invert_contra := let Hcon := fresh "Hcon" in intros Hcon; destruct Hcon as [Hcon | Hcon]; try solve [inversion Hcon || destruct Hcon].
Ltac solve_substitute := repeat (econstructor || eauto || invert_contra || destruct_invert_contra).
Ltac solve_value_builtin := repeat econstructor.

Ltac invert_neutrals :=
  match goal with
  | H : neutral_value ?n ?t |- False =>
      inversion H; clear H; subst; try invert_neutrals
  | H : neutral ?t |- False =>
      inversion H; clear H; subst; try invert_neutrals
  end.

Ltac decide_neutral :=
  match goal with
  | |- neutral_value ?n ?nv =>
      econstructor; eauto; try decide_neutral
  | |- ?f <> ?f' =>
      let Hcon := fresh "Hcon" in
      try solve [intros Hcon; inversion Hcon]
  end.

Example fact_term_evaluates : exists k,
  fact_term 2 =[k]=> Constant (ValueOf DefaultUniInteger 2).
Proof with (autounfold; simpl; eauto || (try reflexivity) || (try solve [intros Hcon; inversion Hcon])).
(* ADMIT: Factorial should use non-strict term bindings, but we do not model them yet. *)
Admitted.
  (*
  unfold fact_term.
  eexists.
  apply E_LetRec.
  eapply E_LetRec_TermBind.
  simpl.
  eapply E_LetRec_Nil.
  eapply E_Apply... {
    eapply E_LetRec.
    eapply E_LetRec_TermBind.
    simpl.
    eapply E_LetRec_Nil...
  } {
    simpl.
    eapply E_IfFalse... {
      eapply E_NeutralApplyFull...
      eapply FA_Apply...
      eapply FA_Apply...
      eapply FA_Builtin...
    } {
      eapply E_NeutralApplyPartial. {
        intros Hcon.
        invert_neutrals.
        simpl in H5.
        apply PeanoNat.Nat.lt_irrefl in H5...
      } {
        eapply E_NeutralApply...
        decide_neutral...
      } {
        simpl...
        decide_neutral...
      } {
        eapply E_Apply... {
          eapply E_LetRec...
          eapply E_LetRec_TermBind...
        } {
          eapply E_NeutralApplyFull...
          eapply FA_Apply...
          eapply FA_Apply...
          eapply FA_Builtin...
        } {
          simpl...
        } {
          simpl...
          eapply E_IfFalse... {
            eapply E_NeutralApplyFull...
            eapply FA_Apply...
            eapply FA_Apply...
            eapply FA_Builtin...
          }
          eapply E_NeutralApplyPartial. {
            intros Hcon.
            invert_neutrals...
            simpl in H5.
            apply PeanoNat.Nat.lt_irrefl in H5...
          } {
            eapply E_NeutralApply...
            decide_neutral...
          } {
            unfold constInt...
            decide_neutral...
          } {
            eapply E_Apply... {
              eapply E_LetRec...
              eapply E_LetRec_TermBind...
            } {
              eapply E_NeutralApplyFull...
              eapply FA_Apply...
              eapply FA_Apply...
              eapply FA_Builtin...
            } {
              intros Hcon. inversion Hcon.
            } {
              simpl...
              eapply E_IfTrue...
              eapply E_NeutralApplyFull...
              eapply FA_Apply...
              eapply FA_Apply...
              eapply FA_Builtin...
            }
          } {
            simpl...
          } {
            eapply E_NeutralApplyFull...
            eapply FA_Apply...
            eapply FA_Apply...
            eapply FA_Builtin...
          }
        }
      } {
        simpl...
      } {
        eapply E_NeutralApplyFull...
        eapply FA_Apply...
        eapply FA_Apply...
        eapply FA_Builtin...
      }
    }
  }
Qed. *)
