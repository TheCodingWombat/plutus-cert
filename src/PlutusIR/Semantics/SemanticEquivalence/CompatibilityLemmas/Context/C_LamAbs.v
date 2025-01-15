From PlutusCert Require Import
  PlutusIR.Semantics.Dynamic
  PlutusIR.Semantics.SemanticEquivalence.LogicalRelation
  Normalisation.Normalisation
  Util.Map
  CompatibilityLemmas.LamAbs
  Kinding.Kinding
.

Lemma compatibility_C_LamAbs : forall Δ₁ Γ₁ v C1 C2 Δ Γ T T₁ T₁n T₂,
  normalise T₁ T₁n ->
  Δ₁ |-* T₁ : Kind_Base ->
  LR_logically_approximate_context Δ₁ ((v, T₁n) :: Γ₁) C1 C2 Δ Γ T T₂ ->
  LR_logically_approximate_context Δ₁ Γ₁ (C_LamAbs v T₁ C1) (C_LamAbs v T₁ C2) Δ Γ T (Ty_Fun T₁n T₂).

Proof.
  intros Δ₁ Γ₁ v C1 C2 Δ Γ T T₁ T₁n T₂.
  intros H_norm_T₁ H_T₁_K H_approx_C1_C2.

  unfold LR_logically_approximate_context.

  intros e1 e2 H_approx_e1_e2.
  simpl.
  eauto using compatibility_LamAbs.
  (* BREAK BECAUSE OF NEW TY_ABS *)
  admit.
Admitted.

