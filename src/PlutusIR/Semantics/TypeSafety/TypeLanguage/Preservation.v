Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.

Theorem preservation : forall Delta T K Tn,
    Delta |-* T : K ->
    normalise T Tn ->
    Delta |-* Tn : K.
Proof.
(* ADMIT: I had no time to finish this. Should hold according to papers. *)
Admitted.