From Equations Require Import Equations.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** kinds *)
Inductive kind :=
  | Kind_Base : kind
  | Kind_Arrow : kind -> kind -> kind.

(** Types *)
Inductive ty :=
  | Var : string -> ty
  | Lam : string -> kind -> ty -> ty
  | App : ty -> ty -> ty.

(** Values *)
Inductive value : ty -> Prop :=
| v_neutral : forall ty1,
    neutral ty1 ->
    value ty1
| v_abs : forall x K2 ty1,
    value ty1 ->
    value (Lam x K2 ty1)
    
    with neutral : ty -> Prop :=
    | ne_var : forall x,
        neutral (Var x)
    | ne_app : forall ty1 ty2,
        neutral ty1 ->
        value ty2 ->
        neutral (App ty1 ty2).

(** Subst *)
Fixpoint subst (X : string) (U T : ty) : ty :=
  match T with
  | Var Y =>
    if X =? Y then U else Var Y
  | Lam Y K1 T' =>
    if X =? Y then Lam Y K1 T' else Lam Y K1 (subst X U T')
  | App T1 T2 =>
    App (subst X U T1) (subst X U T2)
  end.

(** Capture avoiding substitution*)
Definition rename (X Y : string) (T : ty) := subst X (Var Y) T.

Fixpoint size (T : ty) : nat :=
  match T with
  | Var Y => 1
  | Lam bX K T0 => 1 + size T0
  | App T1 T2 => 1 + size T1 + size T2
  end.

Fixpoint ftv (T : ty) : list string :=
match T with
| Var X =>
    [X]
| Lam X K1 T' =>
    remove string_dec X (ftv T')
| App T1 T2 =>
    ftv T1 ++ ftv T2
end.

Definition fresh (X : string) (U T : ty) : string :=
  "a" ++ X ++ (String.concat "" (ftv U)) ++ (String.concat "" (ftv T)).

Lemma fresh__X : forall X U T,
    X <> fresh X U T.
Proof with eauto.
  intros. intros Hcon.
  induction X; induction (ftv U); induction (ftv T).
  all: simpl in Hcon.
  all: inversion Hcon; subst...
Qed.

Lemma fresh__S : forall X U T,
    ~ In (fresh X U T) (ftv U).
Proof. Abort.

Lemma fresh__T : forall X U T,
    ~ In (fresh X U T) (ftv T).
Proof. Abort.

Lemma rename_preserves_size : forall T X Y,
    size T = size (rename X Y T).
Proof.
  unfold rename.
  induction T; intros; simpl; eauto.
  - destruct (X =? s); eauto.
  - destruct (X =? s); simpl; eauto.
Qed.

Equations? substTCA (X : string) (U T : ty) : ty by wf (size T) :=
  substTCA X U (Var Y) =>
      if X =? Y then U else Var Y ;
  substTCA X U (Lam Y K T) =>
      if X =? Y
        then
          Lam Y K T
        else
          if existsb (eqb Y) (ftv U)
            then
              let Y' := fresh X U T in
              let T' := rename Y Y' T in
              Lam Y' K (substTCA X U T')
            else
              Lam Y K (substTCA X U T) ;
  substTCA X U (App T1 T2) =>
      App (substTCA X U T1) (substTCA X U T2)
  .
Proof.
  all: try solve
    [ lia
    || replace T' with (rename Y Y' T); eauto; rewrite <- rename_preserves_size; eauto
    ].
Qed.

(** Notation *)
Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x y" := (App x y) (in custom stlc at level 1, left associativity).
Notation "\ x : k , y" :=
  (Lam x k y) (in custom stlc at level 90, x at level 99,
                     k custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Notation "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(** Step *)
Reserved Notation "ty '-->' ty'" (at level 40).

(* lambdas are no longer values unless their bodies are values*)
(*  So we will start normalising the body*)
Inductive step : ty -> ty -> Prop :=
  | ST_Abs : forall ty1 ty1' x K2,
      ty1 --> ty1' ->
      Lam x K2 ty1 --> Lam x K2 ty1'
  | ST_AppAbs : forall x K2 v1 v2,
         value v1 -> (* Problematic *)
         value v2 -> 
         App (Lam x K2 v1) v2 --> substTCA x v2 v1
  | ST_App1 : forall ty1 ty1' ty2,
         ty1 --> ty1' ->
         App ty1 ty2 --> App ty1' ty2
  | ST_App2 : forall v1 ty2 ty2',
         value v1 ->
         ty2 --> ty2' ->
         App v1 ty2 --> App v1 ty2'

where "ty '-->' ty'" := (step ty ty').
Hint Constructors step : core.

(** Multistep*)
Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation multistep := (multi step).
Notation "ty1 '-->*' ty2" := (multistep ty1 ty2) (at level 40).

(** The lemma I want to prove about substitutions*)
(* Not true:
(* Counter example:
   t = (\y. y) (x w) --> x w = t', 
   then t[x=\z. v] = (\y. y) ((\z. v) w) --> (\y. y) v, 
   while t'[x=\z. v] = (\z. v) w*)*)
Lemma subst_preserves_step : forall X t t' v,
  t --> t' -> value v -> subst X v t  -->* subst X v t'.
Proof.
  intros X t t' v H H_value_v'.
  generalize dependent t'.
  induction t; intros t' Hstep; inversion Hstep; eauto; subst.
  - shelve. 
  - rename t2 into v2. admit. (* uhm, since t2 and \x:K2,v1 are already values, IHt1 and IHt2 don't tell us anything*)
  - shelve.
  - shelve.
Abort.
