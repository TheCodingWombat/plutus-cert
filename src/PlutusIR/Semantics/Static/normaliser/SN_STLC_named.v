(** * Strong Normalization of System F *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import List AutosubstSsr.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import STLC_named STLC_named_typing ARS.

(** **** Notations *)
Fixpoint multiSubstituteT (sigma : list (string * term)) (T : term) : term :=
  match T with
  | tmvar Y =>
    match lookup Y sigma with
    | Some t => t
    | None => tmvar Y
    end
  | tmlam Y K1 T' => 
  (* TODO: We are currently assuming global uniqueness
    without this assumption, we need:
    1. Remove Y from sigma to get sigma'
    2. Apply sigma' on lambda body*)
    tmlam Y K1 (multiSubstituteT sigma T')
  | tmapp T1 T2 =>
    tmapp (multiSubstituteT sigma T1) (multiSubstituteT sigma T2)
  end.

Fixpoint msubst (sigma : list (string * term)) (T : term) : term :=
  match sigma with
  | [] => T
  | (x, s) :: sigma' => substituteT x s (msubst sigma' T)
  end.

(* Notation for substitution *)
Notation "'[' x ':=' s ']' t" := (msubst [(x, s)] t) (at level 20).

Notation "sigma [[ t ]]" := (msubst sigma t) (at level 20).

(** **** One-Step Reduction *)

(* Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope prop_scope with PROP.
Open Scope prop_scope. *)

Inductive step : term -> term -> Prop :=
| step_beta (x : string) (A : type) (s t : term) :
    step (tmapp (tmlam x A s) t) ([x := t] s)
| step_appL s1 s2 t :
    step s1 s2 -> step (tmapp s1 t) (tmapp s2 t)
| step_appR s t1 t2 :
    step t1 t2 -> step (tmapp s t1) (tmapp s t2)
| step_abs x A s1 s2 :
    step s1 s2 -> step (tmlam x A s1) (tmlam x A s2).

Lemma step_ebeta x A s t u : 
  u = ([x := t] s) -> step (tmapp (tmlam x A s) t) u.
Proof. move->. exact: step_beta. Qed.

(* Note: Study: After replacing a variable with something in sigma
  we can still do the same step as we previously could by red s t, hence: true
  Not true in non-deterministic setting.
*)
Lemma step_subst sigma s t :
  step s t -> step (sigma [[ s ]]) (sigma [[ t ]]).
Proof.
  (* move=> st. elim: st sigma => {s t}; asimpl; eauto using step.
  move=> A s t sigma. apply: step_ebeta. by autosubst.
Qed. *)
Admitted.

(** **** Many-Step Reduction *)

Definition red := star step.

(* Definition sred sigma tau :=
  forall x : var, red (sigma x) (tau x). *)

Lemma red_app s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (tmapp s1 t1) (tmapp s2 t2).
Proof.
  move=> A B. apply: (star_trans (tmapp s2 t1)).
  - apply: (star_hom (tmapp^~ t1)) A => x y. exact: step_appL.
  - apply: star_hom B => x y. exact: step_appR.
Qed.

Lemma red_abs x A s1 s2 : 
  red s1 s2 -> red (tmlam x A s1) (tmlam x A s2).
Proof. apply: star_hom => x' y'. exact: step_abs. Qed.

Lemma red_subst sigma s t : 
  red s t -> red (sigma [[s]]) (sigma [[t]]).
Proof. apply: star_hom => x' y'. exact: step_subst. Qed.

(* Lemma sred_up sigma tau : 
  sred sigma tau -> sred (up sigma) (up tau).
Proof. move=> A [|n] //=. asimpl. apply/red_subst/A. Qed. *)

Global Hint Resolve red_app red_abs 
(* sred_hup  *)
: red_congr.

(* Lemma red_compat sigma tau s :
  sred sigma tau -> red ([x := sigma] s) ([x := tau] s).
Proof.
  elim: s sigma tau; intros; asimpl; eauto with red_congr.
Qed. *)

(* NOTE: A little pen and paper study concludes that this is still true for named. *)
Lemma red_beta x s t1 t2 : step t1 t2 -> red ([x := t1] s) ([x := t2] s).
Proof. 
  (* move=> h. apply: red_compat => -[|n]/=; [exact: star1|exact: starR].  *)
Admitted.

(* Strong Normalization *)

Notation SN := (sn step).

Lemma sn_closed t s : SN (tmapp s t) -> SN s.
Proof. apply: (sn_preimage (h := tmapp^~t)) => x y. exact: step_appL. Qed.

Lemma sn_subst sigma s : SN (sigma [[s]]) -> SN s.
Proof. apply: sn_preimage => x' y'. exact: step_subst. Qed.

(* The Reducibility Candidates/Logical Predicate*)

Definition cand := term -> Prop.

Definition neutral (s : term) : bool :=
  match s with
    | tmlam _ _ _ => false
    | _ => true
  end.

Record reducible (P : cand) : Prop := {
  p_sn : forall s, P s -> SN s;
  p_cl : forall s t, P s -> step s t -> P t;
  p_nc : forall s, neutral s -> (forall t, step s t -> P t) -> P s
}.

Fixpoint L (T : type) : cand :=
  match T with
    | tp_base => SN 
    | tp_arrow A B => fun s => forall t, L A t -> L B (tmapp s t)
  end.

(* TODO: Compare with Inductive instantiation from normalisation in
  PLF: that has a cleaner definition, but restraints the order*)
Definition EL (Gamma : list (string * type)) 
          (sigma : list (string * term)) : Prop :=
  forall x T, lookup x Gamma = Some T ->
    exists t, lookup x sigma = Some t /\ L T t.

Lemma extend_EL (Gamma : list (string * type)) (sigma : list (string * term)) x T t :
  EL Gamma sigma -> L T t -> EL ((x, T) :: Gamma) ((x, t) :: sigma).
Proof.
Admitted.

(* Facts about reducible sets. *)

Lemma reducible_sn : reducible SN.
Proof. constructor; eauto using ARS.sn. by move=> s t [f] /f. Qed.
Global Hint Resolve reducible_sn : core.

Lemma reducible_var P x : reducible P -> P (tmvar x).
Proof. move/p_nc. apply=> // t st. inversion st. Qed.

Lemma L_reducible A :
  reducible (L A).
Proof with eauto using step.
  elim: A => /=[|A ih1 B ih2].
  - apply reducible_sn.
  - constructor.
    + move=> s h. apply: (@sn_closed (tmvar "x")). apply: (p_sn (P := L B))...
      eapply h. eapply reducible_var; eauto.
    + move=> s t h st u la. apply: (p_cl _ (s := tmapp s u))...
    + move=> s ns h t la.
      have snt := p_sn ih1 la.
      elim: snt la => {} t _ ih3 la. apply: p_nc... move=> v st. inv st=> //...
      (* Note: Case L B ([x := t] s0. By using Autosubst's "inv" instead of normal inversion, this goal vanishes. Why? *) (* Todo: Think, this case doesn't happen in db variant*)
      * apply: ih3 => //. exact: (p_cl ih1) la _.
Qed.

Corollary L_sn A s : L A s -> SN s.
Proof. intros Las. assert (reducible (L A)) by apply (L_reducible A).
   apply (p_sn H). assumption.
Qed.

Corollary L_cl T s t : L T s -> step s t -> L T t.
Proof.
  intros Hstep Hst.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_cl H Hstep); assumption.
Qed.

Corollary L_nc T s :
  neutral s -> (forall t, step s t -> L T t) -> L T s.
Proof. 
  intros Hneut Hstep.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_nc H); assumption.
Qed.

Corollary L_var T x : L T (tmvar x).
Proof.
  apply L_nc; first by []. intros t st. inversion st.
Qed. 

Corollary L_cl_star T s t :
  L T s -> red s t -> L T t.
Proof.
  intros Ls red_st. induction red_st.
  - assumption.
  - apply L_cl with y; assumption.
Qed.

(* Closure under beta expansion. *)

Lemma beta_expansion A B x s t :
  SN t -> L A ([x := t] s) ->
  L A (tmapp (tmlam x B s) t).
Proof with eauto.
  move=> snt h. have sns := sn_subst (L_sn h).
  elim: sns t snt h => {} s sns ih1 t. elim=> {} t snt ih2 h.
  apply: L_nc => // u st. inv st => //.
  - inv H2. apply: ih1 => //. apply: L_cl h _. exact: step_subst.
  - apply: ih2 => //. apply: L_cl_star h _. exact: red_beta.
Qed.

(* The fundamental theorem. *)

(* TODO *)
Theorem soundness Gamma s A :
  has_type Gamma s A -> forall sigma,
    EL Gamma sigma -> L A (sigma [[s]]).
Proof with eauto using L_sn. 
  elim=> {Gamma s A} [Gamma X A |Gamma X A s B _ ih sigma EL|Gamma s t A B _ ih1 _ ih2 sigma HEL].
  - (* TODO: My own proof, make it more insightful/to the point*)
    intros HlookupGamma sigma HEL.
    unfold EL in HEL.
    specialize (HEL X A HlookupGamma).
    destruct HEL as [t [HlookupSigma LAt] ].
    (* rewrite HlookupSigma. *)
    (* assumption. *)
    admit.
  - move=> t h.
    (* Moving sigma under lambda yields:
    tmapp (tmlam X' A ((drop X sigma) [[rename X X' s]])) t
    
    which is equal to:
    [X' := t] ((drop X sigma) [[rename X X' s]])

    which is equal to (by msubst starting from the right):
    ((X', t)::(drop X sigma)) [[rename X X' s]]

    Which is the goal.

    While our hypothesis says something about
    (X, t)::sigma [[s]]

    But, if X in sigma, then we can't just drop X 
    from sigma, since a substitution might reintroduce it.


    *)
    unfold msubst. 
    apply: beta_expansion...
    
    fold multiSubstituteT.
    specialize (ih ((X, t)::sigma) (extend_EL EL h)).
        (* Note: When sigma goes under the lambda, X is 
        removed from sigma to yield sigma' 
        (if we implement capture avoidance)
        So then when is [X := t] (sigma' [[s]])
          equal to
          (X, t)::sigma [[s]]?

          I guess when we implement lookup in substitutions 
          to start looking from the left,
          or if we replace :: by an "add" operation which 
          overrides or shadows.
          CHECK: lookup is defined this way!

          So we need lemma?:
          - [X := t] ((drop X sigma) [[s]])) = 
              ((X, t)::sigma) [[s]]

          But that is not true, since sigma can e.g. have
          'Y' that maps to 'X'.
          So this is only part of the problem.


        *)
    admit. (* TODO: Where we always got into trouble*)
    (* Note: Directly true in the case of global uniqueness*)
  - specialize (ih1 _ HEL). specialize (ih2 _ HEL).
    unfold L in ih1. fold L in ih1. apply ih1. apply ih2.
Admitted.

Corollary type_L E s T : has_type E s T -> L T s.
Proof.
  move=> ty. move: (@soundness E s T ty) => h.
  admit. (* TODO: Create some sort of identity subsittution*)
Admitted.

Corollary strong_normalization E s T : has_type E s T -> SN s.
Proof.
  move=>/type_L/L_sn. apply.
Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Ssr")) *)
(* End: *)