From Coq Require Extraction.

From PlutusCert Require Import 
  PlutusIR 
  Normalisation.Normalisation 
  Kinding.Kinding
  Kinding.Checker
  Type_reduction
  Util
  SubstituteTCA
  SN_PIR
  Normaliser
  Normalisation.Preservation
  .
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

Theorem norm_sound Tn {T Δ K} (Hwk : Δ |-* T : K) :
  normaliser_wk Hwk = Tn -> normalise T Tn.
Proof.
  intros.
  unfold normaliser_wk in H.
  destruct SN_normalise in H; eauto.
  subst.
  assumption.
Qed.

Theorem norm_complete Δ K (T Tn : ty) (Hwk : Δ |-* T : K):
  normalise T Tn -> normaliser_wk Hwk = Tn.
Proof.
  intros HnormR.
  unfold normaliser_wk.
  destruct SN_normalise.
  simpl.
  now apply (normalisation__deterministic T x Tn) in n.
Qed.

From Coq Require Import ssreflect.

Theorem normaliser_sound Δ T Tn :
  normaliser Δ T = Some Tn -> normalise T Tn.
Proof.
  unfold normaliser.
  move: eq_refl.
  case: {2 3}(kind_check Δ T) => // a e H. (* TODO: I don't understand (all of) this ssreflect stuff, see https://stackoverflow.com/questions/47345174/using-destruct-on-pattern-match-expression-with-convoy-pattern*)
  inversion H.
  eapply norm_sound; eauto.
Qed.

(* We need the well-kinded assumption, otherwise counterexample:
    nil |-* TyApp (Lam bX Kind_Base "bX") (Lam bY Kind_Base "bY")

    which normalises to Lam bY Kind_Base "bY",
    but normaliser _ T will return None

*)
Theorem normaliser_complete {K Δ T Tn} :
  Δ |-* T : K -> normalise T Tn -> normaliser Δ T = Some Tn.
Proof.
  unfold normaliser.
  intros.
  apply kind_checking_complete in H.
  move: eq_refl.
  case: {2 3}(kind_check Δ T) => //.
  - intros.
    f_equal.
    eapply norm_complete; eauto.
  - intros.
    rewrite H in e.
    discriminate.
Qed.

Fixpoint remove_deltas  {A B C : Type} (xs : list (A * B * C)) :=
  match xs with
  | nil => nil 
  | (X, T, _) :: xs' => (X, T) :: (remove_deltas xs')
  end.

Lemma remove_deltas_app {A B C : Type} (xs ys : list (A * B * C)) :
  remove_deltas (xs ++ ys) = remove_deltas xs ++ remove_deltas ys.
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    destruct a.
    destruct p.
    rewrite IHxs.
    reflexivity.
Qed.
    

Lemma map_normaliser_sound xs xs' :
  map_normaliser xs = Some xs' -> map_normalise (remove_deltas xs) xs'.
Proof.
  intros.
  generalize dependent xs'.
  induction xs; intros.
  - inversion H; subst.
    constructor.
  - destruct a as [[X T] Δ].
    apply map_normaliser_unfold in H.
    destruct H as [Tn [xs'' [Heq [Hnorm Hmap]] ] ].
    rewrite Heq.
    constructor.
    + now apply IHxs.
    + eapply normaliser_sound; eauto.
Qed.

Require Import Coq.Program.Equality.

(* Basically we need a map_wellkinded argument *)
Lemma map_normaliser_complete {xs : list (string * ty * (list (string * kind)))} {xs'} :
  map_wk xs -> map_normalise (remove_deltas xs) xs' -> map_normaliser xs = Some xs'.
Proof.
  intros.
  dependent induction H0.
  - simpl.
    assert (xs = []). {
      unfold remove_deltas in x.
      destruct xs; auto.
      fold (@remove_deltas string) in x.
      destruct p as [p0 pff].
      destruct p0 as [X T].
      inversion x.
    }
    subst.
    reflexivity.
  - simpl.
    unfold bind.
    
    inversion H.
    + subst.
      simpl in x.
      inversion x.
    + assert (T = T0). 
      {
        unfold remove_deltas in x.
        destruct xs; [inversion H4 |].
        fold (@remove_deltas string) in x. 
        destruct p as [p0 pff].
        destruct p0 as [X1 T1].
        inversion x.
        subst.
        inversion H4.
        subst.
        reflexivity.
      }
      subst.
      apply (normaliser_complete H3) in H1.
      specialize (IHmap_normalise xs0 H2).
      assert (Ts = remove_deltas xs0).
      {
        unfold remove_deltas in x; fold (@remove_deltas string) in x.
        inversion x.
        auto.
      }
      specialize (IHmap_normalise H4).
      unfold map_normaliser.
      rewrite H1.
      simpl.
      fold map_normaliser.
      rewrite IHmap_normalise.
      simpl.
      assert (X = X0).
      {
        unfold remove_deltas in x; fold (@remove_deltas string) in x.
        inversion x.
        subst.
        reflexivity.
      }
      subst.
      reflexivity.
Qed.


Theorem normaliser_preserves_kinding {Δ T Tn K } :
  Δ |-* T : K -> normaliser Δ T = Some Tn -> Δ |-* Tn : K.
Proof.
  intros.
  apply (normaliser_sound) in H0.
  apply (normalisation_preserves_kinding H) in H0; auto.
Qed.