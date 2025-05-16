Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Tymapping.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
From PlutusCert Require Import Util.Tactics.

Import PlutusNotations.

From Coq Require Import Arith.

Import Lists.List.
Import ListNotations.

Local Open Scope list_scope.



(** Empty typability *)

Lemma RV_typable_empty : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->
    (exists Tn, normalise (msubstT (msyn1 rho) T) Tn /\ ([],, [] |-+ v : Tn)) /\
    (exists Tn', normalise (msubstT (msyn2 rho) T) Tn' /\  ([],, [] |-+ v' : Tn')).
Proof.
  intros.
  unfold RV in H.
  destruct H as [Hval__v [Hval__v' HRC]].
  autorewrite with RC in HRC.
  apply eval_result in Hval__v as Hev__v.
  apply HRC in Hev__v; auto.
  clear HRC.
  destruct Hev__v as [e'_f [j' [Hev__e'_f [Htyp__v [Htyp__v' _]]]]].
  apply eval_result in Hval__v'.
  assert (e'_f = v' /\ j' = 0) by (eapply eval__deterministic; eauto).
  destruct H. subst.
  auto.
Qed.

Lemma V_typable_empty : forall k T rho v v',
    V k T rho v v' ->
    (exists Tn, normalise (msubstT (msyn1 rho) T) Tn /\ ([],, [] |-+ v : Tn)) /\
    (exists Tn', normalise (msubstT (msyn2 rho) T) Tn' /\  ([],, [] |-+ v' : Tn')).
Proof.
  intros k T rho v v' H.
  autorewrite with R in H.
  destruct H as [[H1 H2] _ ].
  auto.
Qed.

Lemma RV_typable_empty_1 : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->
    (exists Tn, normalise (msubstT (msyn1 rho) T) Tn /\ ([],, [] |-+ v : Tn)).
Proof. intros. destruct (RV_typable_empty _ _ _ _ _ H H0) as [Htyp__v Htyp__v']. eauto. Qed.

Lemma V_typable_empty_1 : forall k T rho v v',
    V k T rho v v' ->
    (exists Tn, normalise (msubstT (msyn1 rho) T) Tn /\ ([],, [] |-+ v : Tn)).
Proof. intros. destruct (V_typable_empty _ _ _ _ _ H) as [Htyp__v Htyp__v']. eauto. Qed.

Lemma RV_typable_empty_2 : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->
    (exists Tn', normalise (msubstT (msyn2 rho) T) Tn' /\ ([],, [] |-+ v' : Tn')).
Proof. intros. destruct (RV_typable_empty _ _ _ _ _ H H0) as [Htyp__v Htyp__v']. eauto. Qed.

Lemma V_typable_empty_2 : forall k T rho v v',
    V k T rho v v' ->
    (exists Tn', normalise (msubstT (msyn2 rho) T) Tn' /\ ([],, [] |-+ v' : Tn')).
Proof. intros. destruct (V_typable_empty _ _ _ _ _ H) as [Htyp__v Htyp__v']. eauto. Qed.

(** Closedness *)

Lemma RV_closed : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->
    closed v /\ closed v'.
Proof with eauto.
  intros.
  eapply RV_typable_empty in H...
  destruct H as [ [Tn [Hnorm__Tn Htyp__v]] [Tn' [Hnorm__Tn' Htyp__v']]].
  split.
  all: eapply typable_empty__closed...
Qed.

Lemma V_closed : forall k T rho v v',
    V k T rho v v' ->
    closed v /\ closed v'.
Proof with eauto.
  intros.
  eapply V_typable_empty in H...
  destruct H as [ [Tn [Hnorm__Tn Htyp__v]] [Tn' [Hnorm__Tn' Htyp__v']]].
  split.
  all: eapply typable_empty__closed...
Qed.

Lemma RV_closed_1 : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->
    closed v.
Proof with eauto. apply RV_closed. Qed.


Lemma V_closed_1 : forall k T rho v v',
    V k T rho v v' ->
    closed v.
Proof with eauto. apply V_closed. Qed.

Lemma RV_closed_2 : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->
    closed v'.
Proof with eauto. apply RV_closed. Qed.

Lemma V_closed_2 : forall k T rho v v',
    V k T rho v v' ->
    closed v'.
Proof with eauto. apply V_closed. Qed.

(** Equivalence of step-index implies equivalence of RV *)

Lemma RV_equiv : forall k k' T rho e e',
    RV k T rho e e' ->
    k = k' ->
    RV k' T rho e e'.
Proof. intros. subst. eauto. Qed.


Lemma V_equiv : forall k k' T rho e e',
    V k T rho e e' ->
    k = k' ->
    V k' T rho e e'.
Proof. intros. subst. eauto. Qed.

(** Easy access to the RV conditions *)

Lemma RV_error : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->

    (~ is_error v /\ ~ is_error v' ) \/
    (is_error v /\ is_error v').
Proof.
  intros.
  destruct H as [Hval__v [Hval__v' HRC]].
  apply eval_result in Hval__v as Hev__v.
  apply eval_result in Hval__v' as Hev__v'.
  autorewrite with RC in HRC.
  apply HRC in Hev__v as temp; eauto.
  clear HRC.
  destruct temp as [v'' [j'' [Hev__v'' [_ [_ [ [Hnerr [Hnerr' _]] | Herr]]]]]].
  all: assert (v'' = v' /\ j'' = 0) by (eapply eval__deterministic; eauto).
  all: destruct H; subst.
  all: eauto.
Qed.

Lemma V_value : forall k T rho v v',
    V k T rho v v' ->
    value v /\ value v'.
Proof.
  intros.
  autorewrite with R in H.
  destruct_hypos.
  auto.
Qed.

Corollary V_value_1 : forall k T rho v v',
    V k T rho v v' ->
    value v.
Proof.
  intros.
  eapply proj1.
  eauto using V_value.
Qed.

Corollary V_value_2 : forall k T rho v v',
    V k T rho v v' ->
    value v'.
Proof.
  intros.
  eapply proj2.
  eauto using V_value.
Qed.

Lemma RV_condition : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->

    (
      ~ is_error v /\
      ~ is_error v' /\
      (
        match T with

        (* RV for type variable *)
        | Ty_Var a =>
            forall Chi,
              sem rho a = Datatypes.Some Chi ->
              Chi k v v'

        (* RV for type lambda *)
        | Ty_Lam bX K T =>
            False

        (* RV for type application *)
        | Ty_App T1 T2 =>
            False

        (* RV for built-in types *)
        | Ty_Builtin st =>
            exists sv sv',
              (* Determine the shape of v and v'*)
              v = Constant sv /\
              v' = Constant sv' /\
              (* Syntactic equality *)
              v = v'

        (* RV for function types *)
        | Ty_Fun T1n T2n =>
            (* Determine the shape of v and v' *)
            exists x e_body e'_body T1 T1',
              LamAbs x T1 e_body = v /\
              LamAbs x T1' e'_body = v' /\
              (* Extensional equivalence *)
              forall i (Hlt_i : i < k) v_0 v'_0,
                ~ is_error v_0 /\
                ~ is_error v'_0 ->
                RV i T1n rho v_0 v'_0 ->
                RC i T2n rho <{ [x := v_0] e_body }> <{ [x := v'_0] e'_body }>

        (* RV for recursive types *)
        | Ty_IFix Fn Tn =>
            exists v_0 v'_0 F F' T T',
              (* Determine the shape of v and v' *)
              v = IWrap F T v_0 /\
              v' = IWrap F' T' v'_0 /\
              (* Unwrap *)
              forall i (Hlt_i : i < k) K T0n,
                [] |-* (msubstT (msyn1 rho) Tn) : K ->
                [] |-* (msubstT (msyn2 rho) Tn) : K ->
                normalise (unwrapIFix Fn K Tn) T0n ->
                RC i T0n rho v_0 v'_0

        (* RV for universal types *)
        | Ty_Forall bX K T =>
            exists e_body e'_body bY bZ,
              (* Determine the shape of v and v' *)
              v = TyAbs bY K e_body /\
              v' = TyAbs bZ K e'_body /\
              (* Instantiational equivalence *)
              forall T1 T2 Chi,
                [] |-* T1 : K ->
                [] |-* T2 : K ->
                Rel T1 T2 Chi ->
                forall i (Hlt_i : i < k),
                  RC i T ((bX, (Chi, T1, T2)) :: rho) <{ :[bY := T1] e_body }> <{ :[bZ := T2] e'_body }>
        end
      ) \/ (
        is_error v /\
        is_error v'
      )
    ).
Proof.
  intros.
  destruct H as [Hval__v [Hval__v' HRC]].
  apply eval_result in Hval__v as Hev__v.
  apply eval_result in Hval__v' as Hev__v'.
  autorewrite with RC in HRC.
  apply HRC in Hev__v as temp; eauto.
  clear HRC.
  destruct temp as [v'' [j'' [Hev__v'' [_ [_ condition]]]]].
  assert (v'' = v' /\ j'' = 0) by (eapply eval__deterministic; eauto).
  destruct H. subst.
  rewrite Nat.sub_0_r in condition.
  eauto.
Qed.

Corollary RV_syntactic_equality : forall k st rho v v',
    RV k (Ty_Builtin st) rho v v' ->
    0 < k ->

    (
      ~ is_error v /\
      ~ is_error v' /\
      exists sv sv',
        (* Determine the shape of v and v' *)
        v = Constant sv /\
        v' = Constant sv' /\
        (* Syntactic equality *)
        v = v'
    ) \/ (
      is_error v /\
      is_error v'
    ).
Proof. intros. eapply RV_condition in H. all: eauto. Qed.

Corollary RV_functional_extensionality : forall k T1n T2n rho v v',
    RV k (Ty_Fun T1n T2n) rho v v' ->
    0 < k ->

    (
      ~ is_error v /\
      ~ is_error v' /\
      (* Determine the shape of v and v' *)
      exists x e_body e'_body T1 T1',
        LamAbs x T1 e_body = v /\
        LamAbs x T1' e'_body = v' /\
        (* Extensional equivalence *)
        forall i (Hlt_i : i < k) v_0 v'_0,
          ~ is_error v_0 /\ ~ is_error v'_0 ->
          RV i T1n rho v_0 v'_0 ->
          RC i T2n rho <{ [x := v_0] e_body }> <{ [x := v'_0] e'_body }>
    ) \/ (
      is_error v /\
      is_error v'
    ).
Proof. intros. eapply RV_condition in H. all: eauto. Qed.


Corollary V_functional_extensionality  {i k T1 T2 rho v v' w w'} :
  i < k ->
  V k (Ty_Fun T1 T2) rho v v' ->
  V i T1 rho w w' ->
  (forall x T1 e_body,
    v = <{λ x :: T1 , e_body}> ->
    C i T2 rho <{ [x := w] e_body }> <{ v' ⋅ w' }>)
  /\
  (forall f,
    applied f v ->
    C i T2 rho <{ v ⋅ w }> <{ v' ⋅ w' }>
  )
.
Proof.
  intros H_lt H_V1 H_V2.
  autorewrite with R in H_V1.
  destruct_hypos.
  eauto.
Qed.

Corollary RV_unwrap : forall k Fn Tn rho v v' ,
    RV k (Ty_IFix Fn Tn) rho v v' ->
    0 < k ->

    (
      ~ is_error v /\
      ~ is_error v' /\
      (* Determine the shape of v and v' *)
      exists v_0 v'_0 F F' T T',
        v = IWrap F T v_0 /\
        v' = IWrap F' T' v'_0 /\
        (* Unwrap *)
        forall i (Hlt_i : i < k) K T0n,
          [] |-* (msubstT (msyn1 rho) Tn) : K ->
          [] |-* (msubstT (msyn2 rho) Tn) : K ->
          normalise (unwrapIFix Fn K Tn) T0n ->
          RC i T0n rho v_0 v'_0
    ) \/ (
      is_error v /\
      is_error v'
    ).
Proof. intros. eapply RV_condition in H. all: eauto. Qed.

Corollary RV_instantiational_extensionality : forall k bX K T rho v v',
    RV k (Ty_Forall bX K T) rho v v' ->
    0 < k ->

    (
      ~ is_error v /\
      ~ is_error v' /\
      exists e_body e'_body bY bZ,
        (* Determine the shape of v and v' *)
        v = TyAbs bY K e_body /\
        v' = TyAbs bZ K e'_body /\
        (* Instantiational equivalence *)
        forall T1 T2 Chi,
          [] |-* T1 : K ->
          [] |-* T2 : K ->
          Rel T1 T2 Chi ->
          forall i (Hlt_i : i < k),
            RC i T ((bX, (Chi, T1, T2)) :: rho) <{ :[bY := T1] e_body }> <{ :[bZ := T2] e'_body }>
    ) \/ (
      is_error v /\
      is_error v'
    ).
Proof. intros. eapply RV_condition in H. all: eauto. Qed.

(** Tymapping extension *)

Lemma RV_extend_rho : forall X Chi T1 T2 rho k T v v',
    RV k T rho v v' ->
    RV k T ((X, (Chi, T1, T2)) :: rho) v v'.
Proof with eauto.
  intros.
  remember H as H0.
  clear HeqH0.
  destruct H0 as [Hval__v [Hval__v' HRC]].
  apply eval_result in Hval__v as Hev__v.
  unfold RV.
  split... split...
  autorewrite with RC.
  intros j Hlt__j e_f Hev__e_f.
  assert (e_f = v /\ j = 0) by (eapply eval__deterministic; eauto).
  destruct H0. subst.
  exists v', 0. split. eapply eval_result...
  apply RV_condition in H...
(* ADMIT: We admit this, but this is not entirely correct. This lemma
   is only correct if X does not appear
   freely in the type annotations and types of v and v'.
   Should hold if the uniqueness property holds.

   Jacco: v and v' will be closed if they are in RV, so the assumption
   should just be that X is not free in T.
   Or in other words, X is not in rho/Δ.

   This should follow from the structure of Δ once the type system disallows
   shadowing altogether (https://github.com/jaccokrijnen/plutus-cert/issues/16)

*)
Admitted.



Lemma V_extend_rho : forall X Chi T1 T2 rho k T v v',
    V k T rho v v' ->
    V k T ((X, (Chi, T1, T2)) :: rho) v v'.
(* ADMIT: We admit this, but this is not entirely correct. This lemma
   is only correct if X does not appear
   freely in the type annotations and types of v and v'.
   Should hold if the uniqueness property holds.

   Jacco: v and v' will be closed if they are in RV, so the assumption
   should just be that X is not free in T. Or in other words, X is not in rho/Δ.

   This should follow from the structure of Δ once the type system disallows
   shadowing altogether (https://github.com/jaccokrijnen/plutus-cert/issues/16)

*)
Admitted.
