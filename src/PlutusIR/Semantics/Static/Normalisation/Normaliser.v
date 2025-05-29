From PlutusCert Require Import 
  PlutusIR 
  Normalisation.Normalisation 
  Kinding.Kinding
  Kinding.Checker
  Type_reduction
  Util
  SubstituteTCA
  SN_PIR
  SN_STLC_GU
  Progress
  Normalisation.Preservation
  .

Require Import mathcomp.ssreflect.ssreflect.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

Lemma normalise_extend T1 T2 T3 :
  step T1 T2 -> normalise T2 T3 -> normalise T1 T3.
Proof.
  intros Hstep Hnorm.
  generalize dependent T3.
  induction Hstep; intros T3 Hnorm; try solve [inversion Hnorm; try constructor; eauto].
  eapply N_BetaReduce; eauto.
  + apply N_TyLam.
    now apply normalisation__stable'__normal.
  + now apply normalisation__stable'__normal.
  + (* ADMIT: Unimplemented TY_SOP *) admit.
Admitted.

Definition SN := @sn ty Type_reduction.step.

(* Wouter's suggestion: do not use explicit normalizer in soundness proof*)
Theorem SN_normalise t Δ K :
  Δ |-* t : K -> SN t -> {t' & normalise t t'}.
Proof.
  intros HWK HSN.
  induction HSN as [t].
  destruct (step_dec t Δ K HWK).
  - destruct s0 as [t' Ht_steps].
    remember (step_preserves_kinding Δ K HWK Ht_steps) as Ht'_kind.
    specialize (H t' Ht_steps Ht'_kind) as [tn normt'].
    exists tn. now apply normalise_extend with (T2 := t').
  - exists t.
    now apply normalisation__stable'__normal.
Defined.

(* A gas powered normalizer that does not use the strong normalization result*)
Fixpoint normaliser_gas (n : nat) {T Δ K} (Hwk : Δ |-* T : K) :=
  match n with
    | O => T
    | S n' => 
        match step_dec T Δ K Hwk with
        | inl (existT _ T' P) => 
            let Hwk' := @step_preserves_kinding T T' Δ K Hwk P in
            normaliser_gas n' Hwk'
        | inr _ => T
        end
  end.

Definition normaliser_wk {T Δ K} (Hwk : Δ |-* T : K) : ty :=
  let HSN := plutus_ty_strong_normalization T Δ K Hwk in
  projT1 (SN_normalise T Δ K Hwk HSN).

Definition normaliser Δ T : option ty :=
  match kind_check Δ T with
  | Some K => fun Hkc =>
      Some (normaliser_wk (kind_checking_sound Δ T K Hkc))
  | None => fun _ => None
  end eq_refl.

Theorem normaliser__well_kinded Δ T Tn :
  normaliser Δ T = Some Tn -> {K & Δ |-* T : K}.
Proof.
  unfold normaliser.
  move: eq_refl.
  case: {2 3}(kind_check Δ T) => // a e H. (* TODO: I don't understand (all of) this ssreflect stuff, see https://stackoverflow.com/questions/47345174/using-destruct-on-pattern-match-expression-with-convoy-pattern*)
  inversion H.
  intros.
  exists a.
  now apply kind_checking_sound.
Qed.

Fixpoint map_normaliser (xs : list (string * ty * (list (string * kind)))) :=
  match xs with
  | nil => Some nil
  | ((X, T, Δ) :: xs') => normaliser Δ T >>= fun Tn => 
                     map_normaliser xs' >>= fun xs'' =>
                     Some ((X, Tn) ::xs'')
  end.

Lemma map_normaliser_unfold {Δ : list (string * kind)} {X T} {xs xs'} :
  map_normaliser ((X, T, Δ) :: xs) = Some xs'
  -> exists Tn xs'', (xs' = (X, Tn)::xs'') /\ normaliser Δ T = Some Tn /\ (map_normaliser xs = Some xs'').
Proof.
  intros.
  inversion H.
  unfold bind in H1.
  repeat destruct_match.
  inversion H1.
  exists t.
  exists l.
  auto.
Qed.

Lemma map_normaliser__well_kinded xs xs' :
  map_normaliser xs = Some xs' -> map_wk xs.
Proof.
  intros.
  generalize dependent xs'.
  induction xs; intros.
  - inversion H; subst.
    constructor.
  - destruct a as [[X T] Δ].
    apply map_normaliser_unfold in H.
    destruct H as [Tn [xs'' [Heq [Hnorm Hmap]] ] ].
    apply normaliser__well_kinded in Hnorm as [K Hwk].
    apply MW_cons with (K := K).
    + apply (IHxs xs''); auto.
    + assumption.
Qed.