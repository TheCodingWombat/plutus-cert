From Equations Require Import Equations.
From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import Analysis.FreeVars.
Import Ty.
  
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

(** * Regular substitution of types *)

Fixpoint substituteT (X : string) (U T : ty) : ty :=
  match T with
  | Ty_Var Y =>
    if X =? Y then U else Ty_Var Y
  | Ty_Fun T1 T2 =>
    Ty_Fun (substituteT X U T1) (substituteT X U T2)
  | Ty_IFix F T =>
    Ty_IFix (substituteT X U F) (substituteT X U T)
  | Ty_Forall Y K T' =>
    if X =? Y then Ty_Forall Y K T' else Ty_Forall Y K (substituteT X U T')
  | Ty_Builtin u =>
    Ty_Builtin u
  | Ty_Lam Y K1 T' =>
    if X =? Y then Ty_Lam Y K1 T' else Ty_Lam Y K1 (substituteT X U T')
  | Ty_App T1 T2 =>
    Ty_App (substituteT X U T1) (substituteT X U T2)
  end.

(** Multi-substitutions of types*)
Fixpoint msubstT (ss : list (string * ty)) (T : ty) : ty :=
  match ss with
  | nil => T
  | (a, T0) :: ss' => msubstT ss' (substituteT a T0 T)
  end.

(** * Capture-avoiding substitution of types *)
Require Import Lia.
Import ListNotations.

#[local]
Definition ftv := Ty.ftv.

(** Assume that we compute the substitution of U for X in (LamAbs Y K T).
    We reduce the  problem of generating a fresh type variable to generating
    a type variable A such that:

    A <> X /\ ~ In A (ftv U) /\ ~ In A (ftv T)

    We generate a ``fresh'' type variable naively: We concatenate X, all
    free type variables in U and all free type variables in T together.
    By appending an arbitrary letter such as "a" to the result of the previous,
    we get a type variable string which is strictly larger than [X], the
    free type variables in U and the free type variables in T. This means
    that the abovementioned formula holds.

    TODO: The above is only an informal proof, so we should prove freshness
    formally as well.
*)
Definition fresh (X : string) (U T : ty) : string :=
  "a" ++ X ++ (concat EmptyString (ftv U)) ++ (concat EmptyString (ftv T)).

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

Definition rename (X Y : string) (T : ty) := substituteT X (Ty_Var Y) T.

Fixpoint size (T : ty) : nat :=
  match T with
  | Ty_Var Y => 1
  | Ty_Fun T1 T2 => 1 + size T1 + size T2
  | Ty_IFix F T => 1 + size F + size T
  | Ty_Forall bX K T0 => 1 + size T0
  | Ty_Builtin u => 1
  | Ty_Lam bX K T0 => 1 + size T0
  | Ty_App T1 T2 => 1 + size T1 + size T2
  end.

Lemma rename_preserves_size : forall T X Y,
    size T = size (rename X Y T).
Proof.
  unfold rename.
  induction T; intros; simpl; eauto.
  - destruct (X =? t); eauto.
  - destruct (X =? b); simpl; eauto.
  - destruct (X =? b); simpl; eauto.
Qed.

Equations? substituteTCA (X : string) (U T : ty) : ty by wf (size T) :=
  substituteTCA X U (Ty_Var Y) =>
      if X =? Y then U else Ty_Var Y ;
  substituteTCA X U (Ty_Fun T1 T2) =>
      Ty_Fun (substituteTCA X U T1) (substituteTCA X U T2) ;
  substituteTCA X U (Ty_IFix F T) =>
      Ty_IFix (substituteTCA X U F) (substituteTCA X U T) ;
  substituteTCA X U (Ty_Forall Y K T) =>
      if X =? Y
        then
          Ty_Forall Y K T
        else
          if existsb (eqb Y) (ftv U)
            then
              let Y' := fresh X U T in
              let T' := rename Y Y' T in
              Ty_Forall Y' K (substituteTCA X U T')
            else
              Ty_Forall Y K T ;
  substituteTCA X U (Ty_Builtin u) =>
      Ty_Builtin u ;
  substituteTCA X U (Ty_Lam Y K T) =>
      if X =? Y
        then
          Ty_Lam Y K T
        else
          if existsb (eqb Y) (ftv U)
            then
              let Y' := fresh X U T in
              let T' := rename Y Y' T in
              Ty_Lam Y' K (substituteTCA X U T')
            else
              Ty_Lam Y K (substituteTCA X U T) ;
  substituteTCA X U (Ty_App T1 T2) =>
      Ty_App (substituteTCA X U T1) (substituteTCA X U T2)
  .
Proof.
  all: try solve
    [ lia
    || replace T' with (rename Y Y' T); eauto; rewrite <- rename_preserves_size; eauto
    ].
Qed.

(** Multi-substitutions of types*)
Fixpoint msubstTCA (ss : list (string * ty)) (T : ty) : ty :=
  match ss with
  | nil => T
  | (a, T0) :: ss' => msubstTCA ss' (substituteTCA a T0 T)
  end.
