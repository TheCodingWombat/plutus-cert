Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.Misc.Axiom.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.

Require Import Lists.List.
Import ListNotations.

(*
Fundamental property (reflexivity) of LR_logically_approximate
*)

Definition P_has_type Δ Γ e T :=
  LR_logically_approximate Δ Γ e e T.

Definition P_constructor_well_formed Δ c Tr := Δ |-ok_c c : Tr.

Definition P_bindings_well_formed_nonrec Δ Γ (bs : list binding) :=
  forall Δ_t Γ_t bsGn t t' Tn,
    Δ_t = flatten (List.map binds_Delta bs) ++ Δ ->
    map_normalise (flatten (List.map binds_Gamma bs)) bsGn ->
    Γ_t = bsGn ++ Γ ->
    Δ |-* Tn : Kind_Base ->
    LR_logically_approximate Δ_t Γ_t t t' Tn ->
    LR_logically_approximate Δ Γ (Let NonRec bs t) (Let NonRec bs t') Tn.

Definition P_bindings_well_formed_rec Δ Γ bs1 := Δ ,, Γ |-oks_r bs1.

Definition P_binding_well_formed Δ Γ b :=
  forall Δ_t Γ_t bsGn t t' Tn bs bs',
    Δ_t = binds_Delta b ++ Δ ->
    map_normalise (binds_Gamma b) bsGn ->
    Γ_t = bsGn ++ Γ ->
    Δ |-* Tn : Kind_Base ->
    LR_logically_approximate Δ_t Γ_t (Let NonRec bs t) (Let NonRec bs' t') Tn ->
    LR_logically_approximate Δ Γ (Let NonRec (b :: bs) t) (Let NonRec (b :: bs') t') Tn.

#[export] Hint Unfold
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed : core.

  Local Open Scope list_scope.
  Require Import Coq.Lists.List.

Lemma LR_reflexivity : forall Δ Γ e T,
    Δ ,, Γ |-+ e : T ->
    LR_logically_approximate Δ Γ e e T.
    (* P_has_type Δ Γ e T. *)
Proof with eauto.
  apply has_type__ind with
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).

  all : autounfold; intros; subst.
  all : eauto with DSP_compatibility_lemmas typing.
  - (* BREAK BECAUSE OF NEW TYABS *)
    admit.
  - rewrite flatten_app in H5.
    apply map_normalise__app in H5.
    destruct H5 as [l1n [l2n [Hmn__l1n [Hmn__l2n Heq]]]].
    subst.
    eapply map_normalise__deterministic in H1...
    subst.

    eapply H0...
    eapply H3...
    + eapply Kinding.weakening...
      destruct b.
      * simpl. eapply inclusion_refl.
      * simpl. destruct t0. simpl.
        unfold inclusion.
        intros.
        destruct (b =? x)%string eqn:Heqb.
        -- eapply eqb_eq in Heqb as Heq.
           subst.
           assert (appears_bound_in_ann x (Let NonRec (TypeBind (TyVarDecl x k) t1 :: bs) t)) by eauto.
           eapply uniqueness' in H4.
           rewrite H4 in H1.
           inversion H4.
        -- apply eqb_neq in Heqb as Hneq.
           simpl. rewrite Heqb...
      * destruct d.
        simpl. destruct t0.
        simpl.
        unfold inclusion.
        intros.
        destruct (b0 =? x)%string eqn:Heqb.
        -- eapply eqb_eq in Heqb as Heq.
           subst.
           assert (appears_bound_in_ann x (Let NonRec (DatatypeBind (Datatype (TyVarDecl x k) l b l0) :: bs) t)) by eauto.
           eapply uniqueness' in H4.
           rewrite H4 in H1.
           inversion H4.
        -- apply eqb_neq in Heqb as Hneq.
           simpl. rewrite Heqb...
    + rewrite app_assoc...
      rewrite app_assoc...
      rewrite <- flatten_app...
Admitted.


(* Reflexivity of one-hole contexts *)

From PlutusCert Require Import
  CompatibilityLemmas.Context.C_LamAbs
  CompatibilityLemmas.Context.C_Apply_L
  CompatibilityLemmas.Context.C_Apply_R
  CompatibilityLemmas.Context.C_Hole.

Create HintDb hintdb_compat_context.
#[global]
Hint Resolve
  compatibility_C_Hole
  compatibility_C_LamAbs
  compatibility_C_Apply_L
  compatibility_C_Apply_R

  LR_reflexivity
  : hintdb_compat_context.

#[global]
Hint Unfold P_has_type : hintdb_compat_context.

Lemma LR_reflexivity_context : forall C Δ₁ Γ₁ Δ Γ T T₁,
  Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ T) ↝ T₁ ->
  LR_logically_approximate_context Δ₁ Γ₁ C C Δ Γ T T₁.
Proof with eauto with hintdb_compat_context.
  induction C.

  all: intros Δ₁ Γ₁ Δ Γ T T₁ H_C_ty.
  all: inversion H_C_ty; subst...
  (* BREAK BECAUSE OF TYABS *)
  admit.
Admitted.
