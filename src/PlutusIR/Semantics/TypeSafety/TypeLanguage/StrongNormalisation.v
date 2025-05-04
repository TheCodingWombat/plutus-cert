Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.TypeSubstitution.

Theorem strong_normalisation : forall Delta T K,
    Delta |-* T : K ->
    exists Tn, normalise T Tn.
Proof.
(* ADMIT: I had no time to finish this. Should hold according to papers. *)
Admitted.