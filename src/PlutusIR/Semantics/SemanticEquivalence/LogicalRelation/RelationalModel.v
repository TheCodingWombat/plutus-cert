Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Tymapping.
Require Import PlutusCert.Util.List.

Import PlutusNotations.

From Coq Require Import Lia.
From Equations Require Import Equations.

Require Import Arith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

Local Open Scope list_scope.
Local Open Scope string_scope.
Require Import Utf8_core.

(* Rel:
Any step-indexed relation χ on values, that is closed w.r.t. a decreasing step-index
*)
Definition Rel (T T' : ty) (χ : nat -> term -> term -> Prop) : Prop :=
  forall j v v',
    χ j v v' -> 0 < j ->
      result v /\ result v' /\ (* TODO: change to value? The use-site should already enforce this*)
      (∃ Tn, normalise T Tn /\ ([] ,, [] |-+ v : Tn)) /\
      (∃ Tn', normalise T' Tn' /\ ([] ,, [] |-+ v' : Tn')) /\
      (∀ i, i <= j -> χ i v v')
.

Definition Rel' (T T' : ty) (χ : nat -> term -> term -> Prop) : Prop :=
  forall j v v',
    χ j v v' ->
      value v /\ value v' /\
      (∃ Tn, normalise T Tn /\ ([] ,, [] |-+ v : Tn)) /\
      (∃ Tn', normalise T' Tn' /\ ([] ,, [] |-+ v' : Tn')) /\
      (∀ i, i <= j -> χ i v v')
.



(** Relation interpational of types as computations and values.

    RV = Relational interpretation for values
    RC = Relation interpretation for computations
*)
Equations? RC (k : nat) (T : ty) (rho : tymapping) (e e' : term) : Prop by wf k :=
  RC k T rho e e' =>
    (* RC *)
    forall j (Hlt_j : j < k) e_f,
      e =[j]=> e_f ->
      exists e'_f j', e' =[j']=> e'_f /\

      (* RV *)
      (exists Tn, normalise (msubstT (msyn1 rho) T) Tn /\ ([] ,, [] |-+ e_f : Tn)) /\
      (exists Tn', normalise (msubstT (msyn2 rho) T) Tn' /\  ([] ,, [] |-+ e'_f : Tn')) /\

      (
        (
          ~ is_error e_f /\
          ~ is_error e'_f /\
          (
            match T with

            (* RV for type variable *)
            | Ty_Var a =>
                forall Chi,
                  sem rho a = Datatypes.Some Chi ->
                  Chi (k - j) e_f e'_f

            (* RV for type lambda *)
            | Ty_Lam X K T0 =>
                False

            (* RV for type application *)
            | Ty_App T1 T2 =>
                False

            (* RV for built-in types *)
            | Ty_Builtin st =>
                exists sv sv',
                  (* Determine the shape of e_f and e'_f *)
                  e_f = Constant sv /\
                  e'_f = Constant sv' /\
                  (* Syntactic equality *)
                  e_f = e'_f

            (* RV for function types *)
            | Ty_Fun T1n T2n =>
                (* Determine the shape of e_f and e'_f *)
                exists x e_body e'_body T1 T1',
                  LamAbs x T1 e_body = e_f /\
                  LamAbs x T1' e'_body = e'_f /\
                  (* Extensional equivalence *)
                  forall i (Hlt_i : i < k - j) v_0 v'_0,
                    ~ is_error v_0 /\ ~ is_error v'_0 ->
                    result v_0 /\ result v'_0 /\
                    RC i T1n rho v_0 v'_0 ->
                    RC i T2n rho <{ [x := v_0] e_body }> <{ [x := v'_0] e'_body }>

            (* RV for recursive types *)
            | Ty_IFix Fn Tn =>
                exists v_0 v'_0 F F' T T',
                  (* Determine the shape of e_f and e'_f *)
                  e_f = IWrap F T v_0 /\
                  e'_f = IWrap F' T' v'_0 /\
                  (* Unwrap *)
                  forall i (Hlt_i : i < k - j) K T0n,
                    [] |-* (msubstT (msyn1 rho) Tn) : K ->
                    [] |-* (msubstT (msyn2 rho) Tn) : K ->
                    normalise (unwrapIFix Fn K Tn) T0n ->
                    RC i T0n rho v_0 v'_0

            (* RV for universal types *)
            | Ty_Forall X K Tn =>
                exists e_body e'_body Y Z,
                  (* Determine the shape of e_f and e_f' *)
                  e_f = TyAbs Y K e_body /\
                  e'_f = TyAbs Z K e'_body /\
                  (* Instantiational equivalence *)
                  forall T1 T2 Chi,
                    [] |-* T1 : K ->
                    [] |-* T2 : K ->
                    Rel T1 T2 Chi ->
                    forall i (Hlt_i : i < k - j),
                      RC i Tn ((X, (Chi, T1, T2)) :: rho) <{ :[Y := T1] e_body }> <{ :[Z := T2] e'_body }>
            end
          )
        ) \/ (
          is_error e_f /\
          is_error e'_f
        )
      ).
Proof. all: lia. Qed.

Definition RV (k : nat) (T : ty) (rho : tymapping) (v v' : term) : Prop :=
  result v /\ result v' /\ RC k T rho v v'.

(** Converting from RC to RV and vice versa *)

Lemma make_RC k T rho e e' :
  (forall j (Hlt_j : j < k) e_f,
    e =[j]=> e_f ->
    exists e'_f j', e' =[j']=> e'_f /\ RV (k - j) T rho e_f e'_f
  ) ->
  RC k T rho e e'.
Proof with auto.
  intros H.
  autorewrite with RC.
  intros.

  assert (
    exists (e'_f : term) (j' : nat),
      e' =[ j' ]=> e'_f /\ RV (k - j) T rho e_f e'_f
      )...
  destruct H1 as [e'_f [j' [H_e'_runs H_RV_e_f_e'_f]]].
  exists e'_f, j'.
  split.
    - assumption.
    - unfold RV in H_RV_e_f_e'_f.
      destruct H_RV_e_f_e'_f as [H_val_e_f [H_val_e'_f H_RC]].
      autorewrite with RC in H_RC.
      assert (H_lt : 0 < k - j).
        { lia. }
      assert (H_eval := eval_result _ H_val_e_f).
      assert (H__ := H_RC 0 H_lt e_f H_eval); clear H_RC.
      destruct H__ as [e'f0 [j'' [H_eval_e'_f HH]]].

      (* Since j is e'_f is a value, we should know that e'f0 = e'_f*)
      assert (H_eval_e'_f_val := eval_result _ H_val_e'_f).
      assert (H_eqs := eval__deterministic _ _ _ H_eval_e'_f _ _ H_eval_e'_f_val).
      destruct H_eqs; subst.

      assert (H_kj0 : forall k j, k - j - 0 = k - j). lia.
      rewrite H_kj0 in HH.
      assumption.
Qed.

Lemma RC_to_RV : forall k T rho e e',
    RC k T rho e e' ->
    forall j (Hlt_j : j < k) e_f,
      e =[j]=> e_f ->
      exists e'_f j', e' =[j']=> e'_f /\
        RV (k - j) T rho e_f e'_f.
Proof.
  intros k T rho e e' HRC j Hlt__j e_f Hev__e_f.
  autorewrite with RC in HRC.
  apply HRC in Hev__e_f as temp; eauto.
  clear HRC.
  destruct temp as [e'_f [j' [Hev__e'_f [Htyp__e_f [Htyp__e'_f H]]]]].
  eexists. eexists.
  split. eauto.
  split. eauto using eval_result, eval_to_result__eval.
  split. eauto using eval_result, eval_to_result__eval.
  autorewrite with RC.
  intros.
  assert (e_f =[0]=> e_f). {
    eapply eval_result.
    eapply eval_to_result__eval.
    eauto.
  }
  assert (e_f0 = e_f /\ j0 = 0) by (eapply eval__deterministic; eauto).
  destruct H2. subst.
  eexists. eexists.
  split. eapply eval_result. eapply eval_to_result__eval. eauto.
  rewrite Nat.sub_0_r.
  eauto.
Qed.

Lemma RV_RC k T rho e e' :
  RC k T rho e e' <->
  (forall j (Hlt_j : j < k) e_f,
    e =[j]=> e_f ->
    exists e'_f j', e' =[j']=> e'_f /\ RV (k - j) T rho e_f e'_f
  ).
Proof.
constructor;
eauto using make_RC, RC_to_RV.
Qed.

Corollary RV_unfolded_to_RV : forall k T rho v v',
    result v /\ result v' /\ RC k T rho v v' ->
    RV k T rho v v'.
Proof. intros. auto. Qed.

Lemma RV_to_RC : forall k T rho v v',
  RV k T rho v v' ->
  RC k T rho v v'.
Proof. intros. apply H. Qed.

(** Kind assignments *)
Definition kass := list (string * kind).

(** RD = Interpretation of kind contexts as type mappings *)
Inductive RD : kass -> tymapping -> Prop :=
  | RD_nil :
      RD nil nil
  | RD_cons : forall ck rho T1 T2 Chi X K,
      [] |-* T1 : K ->
      [] |-* T2 : K ->
      Rel T1 T2 Chi ->
      RD ck rho ->
      RD ((X, K) :: ck) ((X, (Chi, T1, T2)) :: rho).


(** D = Interpretation of kind contexts as type mappings *)
Inductive D : list (string * kind) -> tymapping -> Prop :=
  | D_nil :
      D nil nil
  | D_cons : forall ck rho T1 T2 Chi X K,
      [] |-* T1 : K ->
      [] |-* T2 : K ->
      Rel' T1 T2 Chi ->
      D ck rho ->
      D ((X, K) :: ck) ((X, (Chi, T1, T2)) :: rho)
.

(** Term environment *)
Definition env := list (string * term).
(** Type assignments *)
Definition tass := list (string * ty).

(** RG = Interpretation of type contexts as logically related term environments *)
Inductive RG (rho : tymapping) (k : nat) : tass -> env -> env -> Prop :=
  | RG_nil :
      RG rho k nil nil nil
  | RG_cons : forall x T v1 v2 c e1 e2,
      RV k T rho v1 v2 ->
      normal_Ty T ->
      ~ (is_error v1) ->
      RG rho k c e1 e2 ->
      RG rho k ((x, T) :: c) ((x, v1) :: e1) ((x, v2) :: e2).

Fixpoint closed_env (env : env) :=
  match env with
  | nil => True
  | (x,t) :: env' => closed t /\ closed_env env'
  end.

(** Logical relation: logical approximation

    If $\Gamma \vdash e : \tau$ and $\Gamma \vdash e' : \tau$, then we write
    $\Gamma \vdash e \leq e' : \tau$ to mean that
    for all $k \geq 0$, if $env$ and $env'$ are mappings from variables $x$ to closed
    values that are lated for $k$ steps at $\Gamma$, then $\gamma(e)$ and
    $\gamma(e')$ are related for $k$ steps as computations of type $\tau$.
*)
Definition LR_logically_approximate (Δ : list (string * kind)) (Γ : list (string * ty)) (e e' : term) (T : ty) :=
    (Δ ,, Γ |-+ e : T) /\
    (Δ ,, Γ |-+ e' : T) /\
    forall k ρ γ γ',
      RD Δ ρ ->
      RG ρ k Γ γ γ' ->
      RC k T ρ (msubst γ (msubstA (msyn1 ρ) e)) (msubst γ' (msubstA (msyn2 ρ) e')).

Notation close γ ρ t := (msubst γ (msubstA ρ t)).

Notation "Δ ',,' Γ '|-' e1 ≤ e2 ':' T" := (LR_logically_approximate Δ Γ e1 e2 T)
  ( at level 101
  , e1 at level 0
  , e2 at level 0
  , T at level 0
  , no associativity).

(** Logical relation: logical equivalence

    We say $e$ and $e'$ are logically equivalent, written
    $\Gamma \vdash e \tilde e' : \tau$, if they logically approximate one
    another.
*)

Definition LR_logically_equivalent (Δ : list (string * kind)) (Γ : list (string * ty)) (e e' : term) (T : ty) :=
  LR_logically_approximate Δ Γ e e' T /\ LR_logically_approximate Δ Γ e' e T.



(*
Logical approximation of one-hole contexts
*)
Definition LR_logically_approximate_context Δ₁ Γ₁ C C' Δ Γ T T₁ :=
  forall e e',
    Δ ,, Γ |- e ≤ e' : T ->
    Δ₁ ,, Γ₁ |- (context_fill C e) ≤ (context_fill C' e') : T₁
.



(*
Alternative definition of the relational model

Encodes mutual recursion between RV and RC using an extra parameter.
Reuses RD
Defines an alternative RG which depends on the new RV
*)

Require Import Coq.Arith.Wf_nat.


(** Relation interpational of types as computations and values.

    RV = Relational interpretation for values
    RC = Relation interpretation for computations
*)
Inductive interpretation := I_C | I_V.


(* Termination argument of R

In recursive calls of R:
  - either the step-index decreases
  - or a R V calls R C
We express this in a measure on naturals
*)
Definition measure : (interpretation * nat) -> nat :=
  fun '(i, n) => n * 10 + if i then 1 else 0.

Lemma lt_pair_wf : well_founded (ltof (interpretation * nat) measure).
Proof.
  apply (well_founded_ltof _ measure).
Qed.

Instance wf_pair : WellFounded (ltof _ measure) := lt_pair_wf.

(* Logical relation for closed values and computations *)
Equations? R (i : interpretation) (k : nat) (T : ty) (rho : tymapping) (e e' : term) : Prop by wf (i, k) (ltof _ measure) :=

  R I_C k T rho e e' :=
    ∀ j (Hlt_j : j < k) r,
      e =[j]=> r ->
      ∃ r' j',
        e' =[j']=> r' /\
        (R I_V (k - j) T rho r r' \/ (is_error r /\ is_error r'));

  R I_V k T rho v v' :=
    ( (∃ Tn,
        normalise (msubstT (msyn1 rho) T) Tn /\ ([] ,, [] |-+ v : Tn)) /\
      (∃ Tn',
        normalise (msubstT (msyn2 rho) T) Tn' /\  ([] ,, [] |-+ v' : Tn'))
    ) /\

    (value v /\ value v') /\
    (
      match T with
      | Ty_Var a =>
          ∀ Chi,
            sem rho a = Datatypes.Some Chi ->
            Chi k v v'

      | Ty_Lam X K T0 =>
          False

      | Ty_App T1 T2 =>
          False

      | Ty_Builtin st =>
          exists sv sv',
            v = Constant sv /\
            v' = Constant sv' /\
            v = v'

      | Ty_Fun T1n T2n =>
            ∀ i (Hlt_i : i < k) v_0 v'_0,
              R I_V i T1n rho v_0 v'_0 ->
              (∀ x T1 e_body, v = <{λ x :: T1 , e_body}> ->
                R I_C i T2n rho <{ [x := v_0] e_body }> <{ v' ⋅ v'_0 }>)
              /\
              (∀ f, applied f v ->
                R I_C i T2n rho <{ v ⋅ v_0 }> <{ v' ⋅ v'_0 }>
              )

      | Ty_IFix Fn Tn =>
          exists v_0 v'_0 F F' T T',
            v = IWrap F T v_0 /\
            v' = IWrap F' T' v'_0 /\
            ∀ i (Hlt_i : i < k) K T0n,
              [] |-* (msubstT (msyn1 rho) Tn) : K ->
              [] |-* (msubstT (msyn2 rho) Tn) : K ->
              normalise (unwrapIFix Fn K Tn) T0n ->
              R I_V i T0n rho v_0 v'_0

      | Ty_Forall X K Tn =>
          exists e_body e'_body,
            v = TyAbs X K e_body /\
            v' = TyAbs X K e'_body /\
            ∀ T1 T2 Chi,
              [] |-* T1 : K ->
              [] |-* T2 : K ->
              Rel T1 T2 Chi ->
              ∀ i (Hlt_i : i < k),
                R I_C i Tn ((X, (Chi, T1, T2)) :: rho) <{ :[X := T1] e_body }> <{ :[X := T2] e'_body }>
      end
  ).
Proof.
  all: unfold ltof; simpl; lia.
Qed.

Notation C := (R I_C).
Notation V := (R I_V).

Corollary C_values_to_V k T rho v v' :
    0 < k ->
    value v ->
    value v' ->
    C k T rho v v' ->
    V k T rho v v'.
Proof.
  intros H_gt H_v H_v' H_RC.
  autorewrite with R in H_RC.
  apply value__result in H_v as H_r.
  apply value__result in H_v' as H_r'.
  apply eval_result in H_r.
  apply eval_result in H_r'.
  apply H_RC in H_r as [r' [j' [H_res'2 H_RV]]].
  clear H_RC.
  assert (H_eq := eval__deterministic _ _ _ H_res'2 _  _ H_r' ).
  destruct H_eq. subst.
  destruct H_RV.
  - assert (Hk : k - 0 = k) by lia. rewrite Hk in H.
    assumption.
  - apply value__is_error in H_v.
    destruct H.
    contradiction.
  - assumption.
Qed.

Inductive G (rho : tymapping) (k : nat) : tass -> env -> env -> Prop :=
  | G_nil :
      G rho k nil nil nil
  | G_cons : forall x T v1 v2 c e1 e2,
      V k T rho v1 v2 ->
      normal_Ty T ->
      G rho k c e1 e2 ->
      G rho k ((x, T) :: c) ((x, v1) :: e1) ((x, v2) :: e2)
.

Definition approx Δ Γ e e' T :=
    (Δ ,, Γ |-+ e : T) /\
    (Δ ,, Γ |-+ e' : T) /\
    forall k ρ γ γ',
      D Δ ρ ->
      G ρ k Γ γ γ' ->
      C k T ρ (close γ (msyn1 ρ) e) (close γ' (msyn2 ρ) e').

