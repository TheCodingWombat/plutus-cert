Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.Byte.
Require Import Coq.Lists.List.
Require Import Ascii.
Require Import Eqdep.

From PlutusCert Require Import
  PlutusIR
  Util.List
.

Definition EqDec := fun A : Type => forall x y : A, {x = y} + {x <> y}.

Definition Z_eq_dec := Z.eq_dec.

Create HintDb Eqs.
#[export] Hint Resolve
  Nat.eq_dec Z.eq_dec ascii_dec bool_dec string_dec list_eq_dec
  Pos.eq_dec Byte.byte_eq_dec
  : Eqs
.


Ltac solveEq :=
  intros;
  unfold EqDec;
  decide equality;
  auto with Eqs (* debug auto with Eqs.*)
.


(* work-around to let auto convert between
  EqDec A and its definition forall x y : A, {x = y} + {x <> y} := id.
*)
Definition conv A : EqDec A -> forall x y : A, {x = y} + {x <> y} := id.
Definition conv' A : (forall x y : A, {x = y} + {x <> y}) -> EqDec A := id.
  #[export] Hint Resolve 10 conv conv' : Eqs.


Definition prod_dec A B : EqDec A -> EqDec B -> EqDec (A * B).
solveEq.
Defined.
  #[export] Hint Resolve prod_dec : Eqs.


Definition unit_dec: EqDec unit. Proof. solveEq. Defined.
  #[export] Hint Resolve unit_dec : Eqs.

Definition strictness_dec: EqDec strictness. solveEq. Defined.
  #[export] Hint Resolve strictness_dec : Eqs.

  Definition recursivity_dec : EqDec recursivity. Proof. solveEq. Defined.
  #[export] Hint Resolve recursivity_dec : Eqs.

Definition func_dec : EqDec DefaultFun. Proof. solveEq. Defined.
  #[export] Hint Resolve func_dec: Eqs.

Definition DefaultUni_dec : EqDec DefaultUni. solveEq. Defined.
  #[export] Hint Resolve DefaultUni_dec : Eqs.


Fixpoint Data_dec (x y : Data) : {x = y} + {x <> y}.
  unfold EqDec.
  decide equality.
  all: auto with Eqs.
Defined.
  #[export] Hint Resolve Data_dec : Eqs.

Definition uniType_dec : forall (t : DefaultUni), EqDec (uniType t).
  unfold uniType.
  intro t.
  apply uniType_option_rect.
  all: intros; try solveEq.
  -
    rewrite e1 in *. clear e1.
    intuition.
  - rewrite e2 in *.
    rewrite e3 in *.
    intuition.
  - rewrite e2 in *.
    rewrite e3 in *.
    intuition.
Defined.
#[export] Hint Resolve uniType_dec : Eqs.

Definition dec_uniType : forall (t : DefaultUni), EqDec (uniType t).
Proof.
  destruct t; auto with Eqs.
Qed.

Definition constant_dec  : EqDec constant.
Proof.
  intros x y.
  destruct x as [T v].
  destruct y as [T' v'].
  destruct (DefaultUni_dec T T').
  - subst.
    destruct (dec_uniType _ v v').
    + apply left. congruence.
    + apply right. intros H.
      injection H.
      intro H_sigma_eq.
      inversion_sigma.
      (* eq_rect can only be reduced by invoking UIP on H_sigma_eq1 *)
      assert (H_sigma_eq1 = eq_refl) by apply UIP_refl.
      subst H_sigma_eq1; simpl in H_sigma_eq2.
      tauto.
  - apply right.
    intros H.
    inversion H.
    contradiction.
Qed.
  #[export] Hint Resolve constant_dec : Eqs.

Definition Kind_dec : EqDec kind. solveEq. Defined.
  #[export] Hint Resolve Kind_dec : Eqs.

Definition Ty_dec: EqDec ty. solveEq. Defined.
  #[export] Hint Resolve Ty_dec : Eqs.

Definition VDecl_dec: EqDec vdecl. Proof. solveEq. Defined.
  #[export] Hint Resolve VDecl_dec : Eqs.

Definition TVDecl_dec : EqDec tvdecl. Proof. solveEq. Defined.
  #[export] Hint Resolve TVDecl_dec : Eqs.

Definition DTDecl_dec: EqDec dtdecl. Proof. solveEq. Defined.
  #[export] Hint Resolve DTDecl_dec : Eqs.




Lemma term_dec : forall (x y : term), {x = y} + {x <> y}
  with binding_dec: forall (x y : binding), {x = y} + {x <> y}.
Proof.
  - solveEq.
  - solveEq.
Defined.

Definition pass_dec (name_dec : EqDec name) (p1 p2 : pass) :
  {p1 = p2} + {p1 <> p2}.
  Proof. solveEq. Defined.

Definition pair_dec {a b} (a_dec : EqDec a) (b_dec : EqDec b) : EqDec (a * b).
  Proof. solveEq. Defined.



Section Derived_Eqb.
  (*
    I got tired of the handwritten boolean equality that have to be
    updated with every change in AST (including soundness proofs). They are implied
    by the above definitions.

    If it turns out that these are significantly worse in terms of performance, reconsider
    this approach.
  *)


  Definition Eqb x := x -> x -> bool.
  Definition eq_dec_to_eqb {A} : EqDec A -> Eqb A :=
    fun dec_eq x y =>  match dec_eq x y with
    | left _ => true
    | right _ => false
    end.

  Definition func_eqb : Eqb DefaultFun := eq_dec_to_eqb func_dec.
  Definition unit_eqb : Eqb unit := eq_dec_to_eqb unit_dec.
  Definition strictness_eqb : Eqb strictness := eq_dec_to_eqb strictness_dec.
  Definition recursivity_eqb : Eqb recursivity := eq_dec_to_eqb recursivity_dec.
  Definition DefaultUni_eqb : Eqb DefaultUni := eq_dec_to_eqb DefaultUni_dec.
  Definition uniType_eqb : forall t, Eqb (uniType t) := fun t => eq_dec_to_eqb (uniType_dec t).
  Definition constant_eqb : Eqb constant := eq_dec_to_eqb constant_dec.
  Definition Kind_eqb : Eqb kind := eq_dec_to_eqb Kind_dec.
  Definition Ty_eqb : Eqb ty := eq_dec_to_eqb Ty_dec.
  Definition TVDecl_eqb : Eqb tvdecl := eq_dec_to_eqb TVDecl_dec.
  Definition VDecl_eqb: Eqb vdecl := eq_dec_to_eqb VDecl_dec.
  Definition DTDecl_eqb: Eqb dtdecl := eq_dec_to_eqb DTDecl_dec.
  Definition Term_eqb : Eqb term := eq_dec_to_eqb term_dec.
  Definition Binding_eqb : Eqb binding := eq_dec_to_eqb binding_dec.

  Definition eq_dec_to_eqb__sound {A} (dec : EqDec A)
    : forall (x y : A), (eq_dec_to_eqb dec) x y = true <-> x = y.
  Proof.
    unfold eq_dec_to_eqb.
    intros x y.
    destruct (dec x y).
    - subst. intuition.
    - intuition.
      inversion H.
  Qed.

  Definition func_eqb_eq := eq_dec_to_eqb__sound func_dec.
  Definition unit_eqb_eq := eq_dec_to_eqb__sound unit_dec.
  Definition strictness_eqb_eq := eq_dec_to_eqb__sound strictness_dec.
  Definition recursivity_eqb_eq := eq_dec_to_eqb__sound recursivity_dec.
  Definition DefaultUni_eqb_eq := eq_dec_to_eqb__sound DefaultUni_dec.
  Definition uniType_eqb_eq := fun t => eq_dec_to_eqb__sound (uniType_dec t).
  Definition constant_eqb_eq := eq_dec_to_eqb__sound constant_dec.
  Definition Kind_eqb_eq := eq_dec_to_eqb__sound Kind_dec.
  Definition Ty_eqb_eq := eq_dec_to_eqb__sound Ty_dec.
  Definition TVDecl_eqb_eq := eq_dec_to_eqb__sound TVDecl_dec.
  Definition VDecl_eqb_eq := eq_dec_to_eqb__sound VDecl_dec.
  Definition DTDecl_eqb_eq := eq_dec_to_eqb__sound DTDecl_dec.
  Definition Term_eqb_eq := eq_dec_to_eqb__sound term_dec.
  Definition Binding_eqb_eq := eq_dec_to_eqb__sound binding_dec.


End Derived_Eqb.

(* boolean equality
I define this separately from the dec_* functions to avoid carrying around
proof terms at run-time.
*)

(*
  TODO: do this cleanly with HasEqb/HasEqBool/HasEq
  https://coq.inria.fr/library/Coq.Structures.Equalities.html
*)

Create HintDb reflection.

#[export] Hint Resolve ->
  func_eqb_eq
  unit_eqb_eq
  strictness_eqb_eq
  recursivity_eqb_eq
  DefaultUni_eqb_eq
  uniType_eqb_eq
  constant_eqb_eq
  Kind_eqb_eq
  Ty_eqb_eq
  TVDecl_eqb_eq
  VDecl_eqb_eq
  DTDecl_eqb_eq
  Term_eqb_eq
  Binding_eqb_eq
  : reflection
.

#[export] Hint Resolve <-
  func_eqb_eq
  unit_eqb_eq
  strictness_eqb_eq
  recursivity_eqb_eq
  DefaultUni_eqb_eq
  uniType_eqb_eq
  constant_eqb_eq
  Kind_eqb_eq
  Ty_eqb_eq
  TVDecl_eqb_eq
  VDecl_eqb_eq
  DTDecl_eqb_eq
  Term_eqb_eq
  Binding_eqb_eq
  : reflection
.
(*
  Note [#[export] Hints and name-collision]
  ~~~~~~~~~~~~~~~~

  When adding Nat.eqb_eq to a hint database using "#[export] Hint Resolve ->", Coq
  generates a definition eqb_eq_l2r (note: not qualified by module name
  anymore). The same happens when adding String.eqb_eq, thus causing a naming
  conflict.
  Current work-around is to alias the imported functions.
*)
(* Note [#[export] Hints and name-collision] *)
Definition Z_eqb_eq := Z.eqb_eq.
Definition nat_eqb_eq := Nat.eqb_eq.
Definition string_eqb_eq := String.eqb_eq.
#[export] Hint Resolve ->
  andb_true_iff
  nat_eqb_eq
  Z_eqb_eq
  string_eqb_eq
  Ascii.eqb_eq
  Bool.eqb_true_iff
: reflection.

#[export] Hint Resolve <-
  andb_true_iff
  nat_eqb_eq
  Z_eqb_eq
  string_eqb_eq
  Ascii.eqb_eq
  Bool.eqb_true_iff
: reflection.
Definition andb_and : forall s t, s && t = true -> s = true /\ t = true.
Proof. auto with reflection. Qed.
