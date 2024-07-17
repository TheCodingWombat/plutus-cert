From Equations Require Import Equations.
Require Import PlutusCert.PlutusIR.
Require Import Strings.String.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Import List.
Import ListNotations.
From PlutusCert Require Import Analysis.FreeVars.
Import Ty.
Require Import Bool.
Require Import PlutusCert.Util.Map.
Require Import PlutusCert.Util.List.
Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.Weakening.

Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.SubstituteTCA.

Require Import Lia.

Open Scope string_scope.

(** * Norm: Normalization of STLC *)

(* Hint Constructors multi : core. *)

Declare Custom Entry stlc.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Kind_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (Ty_App x y) (in custom stlc at level 1, left associativity).
Notation "\ x : k , y" :=
  (Ty_Lam x k y) (in custom stlc at level 90, x at level 99,
                     k custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion Ty_Var : tyname >-> ty.

Notation "{ x }" := (Ty_Var x) (in custom stlc at level 1, x constr).

Notation "'*'" := Kind_Base (in custom stlc at level 0).

(* ----------------------------------------------------------------- *)
(* *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).


Notation "'[' x ':=' s ']' t" := (substituteTCA x s t) (in custom stlc).
(* ----------------------------------------------------------------- *)
(** *** Reduction *)

Inductive value : ty -> Prop :=
  | v_abs : forall x K2 ty1,
      value <{\x:K2, ty1}>
  | v_var : forall x,
      value (Ty_Var x). (* TODO, notation for tyvars?*)

Hint Constructors value : core.

Reserved Notation "ty '-->' ty'" (at level 40).

Inductive step : ty -> ty -> Prop :=
  | ST_AppAbs : forall x K2 ty1 v2,
         value v2 ->
         <{(\x:K2, ty1) v2}> --> <{ [x:=v2]ty1 }>
  | ST_App1 : forall ty1 ty1' ty2,
         ty1 --> ty1' ->
         <{ty1 ty2}> --> <{ty1' ty2}>
  | ST_App2 : forall v1 ty2 ty2',
         value v1 ->
         ty2 --> ty2' ->
         <{v1 ty2}> --> <{v1  ty2'}>

where "ty '-->' ty'" := (step ty ty').

Hint Constructors step : core.


(* ---------------------------------------------------------------------
Small step*)
Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation multistep := (multi step).
Notation "ty1 '-->*' ty2" := (multistep ty1 ty2) (at level 40).

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
   not (exists t', R t t').

Notation step_normal_form := (normal_form step).

Lemma value__normal : forall t, value t -> step_normal_form t.
Proof with eauto.
  intros t H.
  induction H; intros [t' Hstep]; inversion Hstep.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Preservation *)

Theorem preservation : forall t t' T,
   [] |-* t : T  ->
   t --> t'  ->
   [] |-* t' : T.
Proof with eauto.
intros t t' T HT. generalize dependent t'.
remember [] as Gamma.
induction HT;
  intros t' HE; subst; inversion HE; subst...
- apply substituteTCA_preserves_kinding with K1...
  inversion HT1...
- (* T_App *)
  inversion HE; subst...
  + (* ST_AppAbs *)
    apply substituteTCA_preserves_kinding with K1...
    inversion HT1...
  + 
    specialize IHHT1 with (ty1').
    specialize (IHHT1 eq_refl).
    apply IHHT1 in H0.
    apply K_App with (K1 := K1); assumption.
  + apply K_App with (K1 := K1); assumption. 
- apply K_App with (K1 := K1); [assumption|].
  apply IHHT2 in H3; [assumption|reflexivity].    
Qed.

(* ----------------------------------------------------------------- *)
(** *** Context Invariance *)

(* TODO: This is kind of already defined in Analysis.FreeVars*)

Inductive appears_free_in : string -> ty -> Prop :=
  | afi_var : forall (x : string),
      appears_free_in x (Ty_Var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x <{ t1 t2 }>
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x <{ t1 t2 }>
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x <{ \y : T11, t12 }>
.

Hint Constructors appears_free_in : core.

Definition closed (t:ty) :=
  forall x, ~ appears_free_in x t.

Lemma context_invariance : forall Gamma Gamma' t K,
     Gamma |-* t : K  ->
     (forall x, appears_free_in x t -> List.lookup x Gamma = List.lookup x Gamma')  ->
     Gamma' |-* t : K.
Proof.
  intros.
  generalize dependent Gamma'.
  induction H; intros; eauto 12.
  - (* T_Var *)
    apply K_Var. rewrite <- H0; auto.
  - (* Ty_Fun *)
    admit.
  - admit.
  - admit.
  - admit.
  - (* T_Abs *)
    apply K_Lam.
    apply IHhas_kind. intros x1 Hafi.
    
    (* the only tricky step... *)
    destruct (eqb_spec X x1); subst.
    + rewrite lookup_eq.
      rewrite lookup_eq.
      reflexivity.
    + rewrite lookup_neq; [| symmetry; assumption].
      rewrite lookup_neq; [| symmetry; assumption].
      auto.
  - (* Ty_App *)
    apply K_App with (K1 := K1).
    + apply IHhas_kind1. intros x1 Hafi.
      auto.
    + apply IHhas_kind2. intros x1 Hafi.
      auto. 
Admitted.

(* A handy consequence of [eqb_neq]. *)
Theorem false_eqb_string : forall x y : string,
   x <> y -> String.eqb x y = false.
Proof.
  intros x y. rewrite String.eqb_neq.
  intros H. apply H. Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |-* t : T ->
   exists T', List.lookup x Gamma = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - (* T_Abs *)
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold lookup in Hctx.
    rewrite false_eqb_string in Hctx...
Qed.

Corollary typable_empty__closed : forall t T,
    [] |-* t : T  ->
    closed t.
Proof.
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  discriminate C.  
Qed.

(* ----------------------------------------------------------------- *)
(** *** Determinism *)

(** To prove determinsm, we introduce a helpful tactic.  It identifies
    cases in which a value takes a step and solves them by using
    value__normal.  *)

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Ltac solve_by_value_nf :=
  match goal with | H : value ?v, H' : ?v --> ?v' |- _ =>
  exfalso; apply value__normal in H; eauto
  end.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Lemma step_deterministic :
   deterministic step.
Proof with eauto.
   unfold deterministic.
   intros t t' t'' E1 E2.
   generalize dependent t''.
   induction E1; intros t'' E2; inversion E2; subst; clear E2;
   try solve_by_invert; try f_equal; try solve_by_value_nf; eauto.
Qed.

(* ################################################################# *)
(** * Normalization *)

(** Now for the actual normalization proof.

    Our goal is to prove that every well-typed term reduces to a
    normal form.  In fact, it turns out to be convenient to prove
    something slightly stronger, namely that every well-typed term
    reduces to a _value_.  This follows from the weaker property
    anyway via Progress (why?) but otherwise we don't need Progress,
    and we didn't bother re-proving it above.

    Here's the key definition: *)

Definition halts  (t:ty) : Prop :=  exists t', t -->* t' /\  value t'.

(** A trivial fact: *)

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros v H. unfold halts.
  exists v. split.
  - apply multi_refl.
  - assumption.
Qed.

(** The key issue in the normalization proof (as in many proofs by
    induction) is finding a strong enough induction hypothesis.  To
    this end, we begin by defining, for each type [T], a set [R_T] of
    closed terms of type [T].  We will specify these sets using a
    relation [R] and write [R T t] when [t] is in [R_T]. (The sets
    [R_T] are sometimes called _saturated sets_ or _reducibility
    candidates_.)

    Here is the definition of [R] for the base language:

    - [R bool t] iff [t] is a closed term of type [bool] and [t] halts
      in a value

    - [R (T1 -> T2) t] iff [t] is a closed term of type [T1 -> T2] and
      [t] halts in a value _and_ for any term [s] such that [R T1 s],
      we have [R T2 (t s)]. *)

(** This definition gives us the strengthened induction hypothesis that we
    need.  Our primary goal is to show that all _programs_ ---i.e., all
    closed terms of base type---halt.  But closed terms of base type can
    contain subterms of functional type, so we need to know something
    about these as well.  Moreover, it is not enough to know that these
    subterms halt, because the application of a normalized function to a
    normalized argument involves a substitution, which may enable more
    reduction steps.  So we need a stronger condition for terms of
    functional type: not only should they halt themselves, but, when
    applied to halting arguments, they should yield halting results.

    The form of [R] is characteristic of the _logical relations_ proof
    technique.  (Since we are just dealing with unary relations here, we
    could perhaps more properly say _logical properties_.)  If we want to
    prove some property [P] of all closed terms of type [A], we proceed by
    proving, by induction on types, that all terms of type [A] _possess_
    property [P], all terms of type [A->A] _preserve_ property [P], all
    terms of type [(A->A)->(A->A)] _preserve the property of preserving_
    property [P], and so on.  We do this by defining a family of
    properties, indexed by types.  For the base type [A], the property is
    just [P].  For functional types, it says that the function should map
    values satisfying the property at the input type to values satisfying
    the property at the output type.

    When we come to formalize the definition of [R] in Coq, we hit a
    problem.  The most obvious formulation would be as a parameterized
    Inductive proposition like this:

      Inductive R : ty -> tm -> Prop :=
      | R_bool : forall b t, empty |-- t \in Bool ->
                      halts t ->
                      R Bool t
      | R_arrow : forall T1 T2 t, empty |-- t \in (Arrow T1 T2) ->
                      halts t ->
                      (forall s, R T1 s -> R T2 (app t s)) ->
                      R (Arrow T1 T2) t.

    Unfortunately, Coq rejects this definition because it violates the
    _strict positivity requirement_ for inductive definitions, which says
    that the type being defined must not occur to the left of an arrow in
    the type of a constructor argument. Here, it is the third argument to
    [R_arrow], namely [(forall s, R T1 s -> R TS (app t s))], and
    specifically the [R T1 s] part, that violates this rule.  (The
    outermost arrows separating the constructor arguments don't count when
    applying this rule; otherwise we could never have genuinely inductive
    properties at all!)  The reason for the rule is that types defined
    with non-positive recursion can be used to build non-terminating
    functions, which as we know would be a disaster for Coq's logical
    soundness. Even though the relation we want in this case might be
    perfectly innocent, Coq still rejects it because it fails the
    positivity test.

    Fortunately, it turns out that we _can_ define [R] using a
    [Fixpoint]: *)

Fixpoint R (T:kind) (t:ty) : Prop :=
  [] |-* t : T /\ halts t /\
  (match T with
   | <{ * }>  => True
   | <{ K1 -> K2 }> => (forall s, R K1 s -> R K2 <{t s}> )
   end).

(** As immediate consequences of this definition, we have that every
    element of every set [R_T] halts in a value and is closed with type
    [T] :*)

Lemma R_halts : forall {T} {t}, R T t -> halts t.
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [_ [H _]]; assumption.
Qed.

Lemma R_typable_empty : forall {T} {t}, R T t -> [] |-* t : T.
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [H _]; assumption.
Qed.

(** Now we proceed to show the main result, which is that every
    well-typed term of type [T] is an element of [R_T].  Together with
    [R_halts], that will show that every well-typed term halts in a
    value.  *)

(* ================================================================= *)
(** **  Membership in [R_T] Is Invariant Under Reduction *)

(** We start with a preliminary lemma that shows a kind of strong
    preservation property, namely that membership in [R_T] is _invariant_
    under reduction. We will need this property in both directions,
    i.e., both to show that a term in [R_T] stays in [R_T] when it takes a
    forward step, and to show that any term that ends up in [R_T] after a
    step must have been in [R_T] to begin with.

    First of all, an easy preliminary lemma. Note that in the forward
    direction the proof depends on the fact that our language is
    determinstic. This lemma might still be true for nondeterministic
    languages, but the proof would be harder! *)

Lemma step_preserves_halting :
  forall t t', (t --> t') -> (halts t <-> halts t').
Proof.
 intros t t' ST.  unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V]].
  destruct STM.
   + exfalso; apply value__normal in V; eauto.
   + rewrite (step_deterministic _ _ _ ST H). exists z. split; assumption.
 - (* <- *)
  intros [t'0 [STM V]].
  exists t'0. split; eauto.
  apply multi_step with (y := t'); assumption.
Qed.

(** Now the main lemma, which comes in two parts, one for each
    direction.  Each proceeds by induction on the structure of the type
    [T]. In fact, this is where we make fundamental use of the
    structure of types.

    One requirement for staying in [R_T] is to stay in type [T]. In the
    forward direction, we get this from ordinary type Preservation. *)

Lemma step_preserves_R : forall T t t', (t --> t') -> R T t -> R T t'.
Proof.
 induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t [halts_t RRt]].
  (* Bool *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  auto.
  (* Arrow *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  intros.
  eapply IHT2.
  apply  ST_App1. apply E.
  apply RRt; auto.
Qed.

(** The generalization to multiple steps is trivial: *)

Lemma multistep_preserves_R : forall T t t',
  (t -->* t') -> R T t -> R T t'.
Proof.
  intros T t t' STM; induction STM; intros.
  assumption.
  apply IHSTM. eapply step_preserves_R. apply H. assumption.
Qed.

(** In the reverse direction, we must add the fact that [t] has type
   [T] before stepping as an additional hypothesis. *)

Lemma step_preserves_R' : forall K t t',
  [] |-* t : K -> (t --> t') -> R K t' -> R K t.
Proof. (* This proof was not in software foundations *)
  induction K; intros t t' E Rt; unfold R; fold R. split.
  - assumption.
  - destruct H as [_ [Hhalts _]].
    split; [|reflexivity].
    apply (step_preserves_halting _ _ Rt).
    assumption.
  - split; [|split].
    + destruct H as [H _].
      assumption.
    + apply (step_preserves_halting _ _ Rt). 
      apply H.
    + assert (forall s, R K1 s -> <{ t s }> --> <{ t' s }> ) by eauto.
      assert (forall s, R K1 s -> [] |-* <{ t s }> : K2).
      {
        intros s HRK1.
        induction K1; unfold R in HRK1; fold R in HRK1
        ; destruct HRK1 as [HRK1 _].
        - apply K_App with (K1 := Kind_Base); assumption.
        - apply K_App with (K1 := <{ K1_1 -> K1_2}>); assumption.   
      }
      assert (forall s, R K1 s -> [] |-* <{ t' s }> : K2).
      {
        intros s HRK1.
        induction K1; unfold R in HRK1; fold R in HRK1
        ; destruct HRK1 as [HRK1 _]; destruct H as [H _].
        - apply K_App with (K1 := Kind_Base); assumption.
        - apply K_App with (K1 := <{ K1_1 -> K1_2}>); assumption.   
      }
      assert (forall s, R K1 s -> R K2 <{t' s}> -> R K2 <{t s}>).
      {
        intros s RK1s.
        apply IHK2 with (t := <{ t s }>) (t' := <{ t' s }>).
        - apply H1.
          assumption.
        - apply H0.
          assumption. 
      }
      destruct H as [_ [_ H]].
      intros s HRK1.
      apply H3.
      * assumption.
      * apply H.
        assumption.
Qed. 


    
  

Lemma multistep_preserves_R' : forall T t t',
  [] |-* t : T -> (t -->* t') -> R T t' -> R T t.
Proof.
  intros T t t' HT STM.
  induction STM; intros.
    assumption.
    eapply step_preserves_R'.  assumption. apply H. apply IHSTM.
    eapply preservation;  eauto. auto.
Qed.

(* ================================================================= *)
(** ** Closed Instances of Terms of Type [t] Belong to [R_T] *)

(** Now we proceed to show that every term of type [T] belongs to
    [R_T].  Here, the induction will be on typing derivations (it would be
    surprising to see a proof about well-typed terms that did not
    somewhere involve induction on typing derivations!).  The only
    technical difficulty here is in dealing with the abstraction case.
    Since we are arguing by induction, the demonstration that a term
    [abs x T1 t2] belongs to [R_(T1->T2)] should involve applying the
    induction hypothesis to show that [t2] belongs to [R_(T2)].  But
    [R_(T2)] is defined to be a set of _closed_ terms, while [t2] may
    contain [x] free, so this does not make sense.

    This problem is resolved by using a standard trick to suitably
    generalize the induction hypothesis: instead of proving a statement
    involving a closed term, we generalize it to cover all closed
    _instances_ of an open term [t].  Informally, the statement of the
    lemma will look like this:

    If [x1:T1,..xn:Tn |-- t : T] and [v1,...,vn] are values such that
    [R T1 v1], [R T2 v2], ..., [R Tn vn], then
    [R T ([x1:=v1][x2:=v2]...[xn:=vn]t)].

    The proof will proceed by induction on the typing derivation
    [x1:T1,..xn:Tn |-- t : T]; the most interesting case will be the one
    for abstraction. *)

(* ----------------------------------------------------------------- *)
(** *** Multisubstitutions, Multi-Extensions, and Instantiations *)

(** However, before we can proceed to formalize the statement and
    proof of the lemma, we'll need to build some (rather tedious)
    machinery to deal with the fact that we are performing _multiple_
    substitutions on term [t] and _multiple_ extensions of the typing
    context.  In particular, we must be precise about the order in which
    the substitutions occur and how they act on each other.  Often these
    details are simply elided in informal paper proofs, but of course Coq
    won't let us do that. Since here we are substituting closed terms, we
    don't need to worry about how one substitution might affect the term
    put in place by another.  But we still do need to worry about the
    _order_ of substitutions, because it is quite possible for the same
    identifier to appear multiple times among the [x1,...xn] with
    different associated [vi] and [Ti].

    To make everything precise, we will assume that environments are
    extended from left to right, and multiple substitutions are performed
    from right to left.  To see that this is consistent, suppose we have
    an environment written as [...,y:bool,...,y:nat,...]  and a
    corresponding term substitution written as [...[y:=(tbool
    true)]...[y:=(const 3)]...t].  Since environments are extended from
    left to right, the binding [y:nat] hides the binding [y:bool]; since
    substitutions are performed right to left, we do the substitution
    [y:=(const 3)] first, so that the substitution [y:=(tbool true)] has
    no effect. Substitution thus correctly preserves the type of the term.

    With these points in mind, the following definitions should make sense.

    A _multisubstitution_ is the result of applying a list of
    substitutions, which we call an _environment_. *)

(** We need similar machinery to talk about repeated extension of a
    typing context using a list of (identifier, type) pairs, which we
    call a _type assignment_. *)

Definition env := list (string * ty).
Definition kass := list (string * kind).

Open Scope list_scope.


Definition mupdate (Gamma : kass) (xts : kass) : kass :=
  xts ++ Gamma.

(** An _instantiation_ combines a type assignment and a value
    environment with the same domains, where corresponding elements are
    in R. *)

Inductive instantiation :  kass -> env -> Prop :=
| V_nil :
    instantiation nil nil
| V_cons : forall x T v c e,
    value v -> R T v ->
    instantiation c e ->
    instantiation ((x,T)::c) ((x,v)::e).

(** We now proceed to prove various properties of these definitions. *)

(* ----------------------------------------------------------------- *)
(** *** More Substitution Facts *)

(** First we need some additional lemmas on (ordinary) substitution. *)

Lemma vacuous_substitution : forall  t x,
     ~ appears_free_in x t  ->
     forall t', <{ [x:=t']t }> = t.
Proof with eauto.
  (* FILL IN HERE *) Admitted.

Lemma subst_closed: forall t,
     closed t  ->
     forall x t', <{ [x:=t']t }> = t.
Proof.
  intros. apply vacuous_substitution. apply H.  Qed.

Lemma subst_not_afi : forall t x v,
    closed v ->  ~ appears_free_in x <{ [x:=v]t }>.
Proof with eauto.  (* rather slow this way *)
  unfold closed, not.
  induction t; intros x v P A; simpl in A.
    - (* var *)
     destruct (eqb_spec x t). 
      + 
        funelim (substituteTCA x v (Ty_Var x)); try discriminate.
        inversion H.
        symmetry in H1.
        rewrite <- H1 in Heqcall.
        rewrite eqb_refl in Heqcall.
        rewrite <- Heqcall in A.
        apply P in A.
        assumption.
      + funelim (substituteTCA x v (Ty_Var t)); try discriminate.
        inversion H.
        rewrite <- H1 in n.
        rewrite <- eqb_neq in n.
        rewrite n in Heqcall.
        rewrite <- Heqcall in A.
        rewrite -> H in A.
        inversion A.
        rewrite <- H1 in H3.
        rewrite <- eqb_eq in H3.
        rewrite -> H3 in n.
        discriminate.
    - admit.
    - admit.
    - admit.
    - admit.
    - (* lam *)
     shelve.
     
    - (* app *)
      funelim (substituteTCA x v <{t1 t2}>); try discriminate.
      rewrite <- Heqcall in A.
      inversion A.
      + apply IHt1 with (x := X) (v := U); [apply P | ].
        inversion H1.
        subst...
      + apply IHt2 with (x := X) (v := U); [apply P | ].
        inversion H1.
        subst...     
Admitted.

Lemma duplicate_subst : forall t' x t v,
  closed v -> <{ [x:=t]([x:=v]t') }> = <{ [x:=v]t' }>.
Proof.
  intros. eapply vacuous_substitution. apply subst_not_afi. assumption.
Qed.

Lemma subst_tyvar_identity : forall x v t,
  x <> t -> <{[x := v] {t}}> = <{{t}}>.
Proof.
  intros x v t Hneq.
  funelim (substituteTCA x v (Ty_Var t)); try discriminate.
  inversion H.
  rewrite <- H1 in Hneq.
  apply eqb_neq in Hneq.
  rewrite Hneq in Heqcall.
  rewrite <- Heqcall.
  rewrite -> H1.
  reflexivity.
Qed.

Lemma subst_tyvar_value : forall x v ,
  <{[x := v] {x}}> = <{v}>.
Proof.
  intros x v.
  funelim (substituteTCA x v (Ty_Var x)); try discriminate.
  inversion H.
  rewrite H1 in Heqcall.
  rewrite eqb_refl in Heqcall.
  rewrite <- Heqcall.
  reflexivity.
Qed.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v -> closed v1 ->
    <{ [x1:=v1]([x:=v]t) }> = <{ [x:=v]([x1:=v1]t) }>.
Proof with eauto.
 induction t; intros; simpl.
  - (* var *)
   destruct (eqb_spec x t); destruct (eqb_spec x1 t).
   + subst. exfalso...
   + subst. simpl. rewrite subst_closed.
    * rewrite -> subst_tyvar_identity with (x := x1). reflexivity. assumption. 
    * rewrite -> subst_tyvar_value.
      assumption.  
   + rewrite -> subst_tyvar_identity with (x := x); [|assumption].
     subst.
     rewrite subst_tyvar_value.
     rewrite subst_closed; [reflexivity | assumption].
   + rewrite subst_tyvar_identity; [|assumption].
     rewrite subst_tyvar_identity; [|assumption].
     rewrite subst_tyvar_identity; [|assumption].
     reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
  - shelve.
  - shelve.
Admitted. 

(* ----------------------------------------------------------------- *)
(** *** Properties of Multi-Substitutions *)

Lemma msubstTCA_closed: forall t, 
  closed t -> forall ss, msubstTCA ss t = t.
Proof.
  induction ss.
    reflexivity.
    destruct a. simpl. rewrite subst_closed; assumption.
Qed.

(** Closed environments are those that contain only closed terms. *)

Fixpoint closed_env (env:env) :=
  match env with
  | nil => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.

(** Next come a series of lemmas charcterizing how [msubst] of closed terms
    distributes over [subst] and over each term form *)

Lemma subst_msubstTCA: forall env x v t, closed v -> closed_env env ->
    msubstTCA env <{ [x:=v]t }> = substituteTCA x v (msubstTCA (drop x env) t).
Proof.
  induction env0; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (eqb_spec s x).
  - subst. rewrite duplicate_subst; auto.
  - simpl. rewrite swap_subst; eauto.
Qed.

Lemma msubstTCA_var:  forall ss x, closed_env ss ->
   msubstTCA ss (Ty_Var x) =
   match lookup x ss with
   | Some t => t
   | None => Ty_Var x
  end.
Proof.
  induction ss; intros; [reflexivity|].
  destruct a as [ax aty].
  remember (if x =? ax then aty else Ty_Var x) as t'.
  simpl.
  destruct (eqb_spec ax x).
  - subst... rewrite -> subst_tyvar_value.
    simpl in H; destruct H as [H _].
    apply msubstTCA_closed.
    assumption.
  - rewrite -> subst_tyvar_identity; [|assumption].
    simpl in H; destruct H as [_ H].
    rewrite IHss; [reflexivity|assumption]. 
Qed.


(* This is not true because of renaming, but I think I can still kind of use it*)
Lemma substTCA_abs: forall X1 K1 X2 K2 T,
  substituteTCA X1 K1 (Ty_Lam X2 K2 T) =
    if X1 =? X2 then Ty_Lam X2 K2 T else Ty_Lam X2 K2 (substituteTCA X1 K1 T).
Proof.
Admitted.

(* TODO: This is not true because of renaming, but let's just assume that it is lol *)
Lemma msubstTCA_abs: forall ss x T t,
  msubstTCA ss <{ \ x : T, t }> = Ty_Lam x T (msubstTCA (drop x ss) t).
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. destruct (String.eqb s x); simpl; auto.
Admitted.

(* (* TODO: I also don't think this one holds. 
  BUt now I do, because msubstTCA is defined as first 
  substituting the X for the v *)
  (* I think it holds by the fact that a lambda, after substitution, is still a lambda, and thus a value*)
  (* So it might be problematic if we start normalising the bodies? But not really, 
  because we will assume the bodies ar enormalising? *)
Lemma msubstTCA_beta: forall ss X K ty v,
  Ty_App (msubstTCA ss (Ty_Lam X K ty)) v -->* msubstTCA ((X, v)::ss) ty.
Proof.
Admitted. *)


Lemma msubstTCA_app : forall ss t1 t2,
    msubstTCA ss <{ t1 t2 }> = Ty_App (msubstTCA ss t1) (msubstTCA ss t2).
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. auto.
Admitted.

(** You'll need similar functions for the other term constructors. *)

(* FILL IN HERE *)

(* ----------------------------------------------------------------- *)
(** *** Properties of Multi-Extensions *)

(** We need to connect the behavior of type assignments with that of
    their corresponding contexts. *)

(* Lemma mupdate_lookup : forall (c : kass) (x:string),
    lookup x c = lookup x c.
Proof.
Admitted. TODO: This lemma is not necessary anymore since we use lists instead of partial maps *)

(* Lemma mupdate_drop : forall (c: kass) Gamma x x',
      mupdate Gamma (drop x c) x'
    = if String.eqb x x' then Gamma x' else mupdate Gamma c x'.
Proof.
  induction c; intros.
  - destruct (eqb_spec x x'); auto.
  - destruct a. simpl.
    destruct (eqb_spec s x).
    + subst. rewrite IHc.
      unfold update, t_update. destruct (eqb_spec x x'); auto.
    + simpl. unfold update, t_update. destruct (eqb_spec s x'); auto.
      subst. rewrite false_eqb_string; congruence.
Qed. *)

(* ----------------------------------------------------------------- *)
(** *** Properties of Instantiations *)

(** These are strightforward. *)

Lemma instantiation_domains_match: forall {c} {e},
    instantiation c e ->
    forall {x} {T},
      lookup x c = Some T -> exists t, lookup x e = Some t.
Proof.
  intros c e V. induction V; intros x0 T0 C.
    solve_by_invert.
    simpl in *.
    destruct (String.eqb x x0); eauto.
Qed.

Lemma instantiation_env_closed : forall c e,
  instantiation c e -> closed_env e.
Proof.
  intros c e V; induction V; intros.
    econstructor.
    unfold closed_env. fold closed_env.
    split; [|assumption].
    eapply typable_empty__closed. eapply R_typable_empty. eauto.
Qed.

Lemma instantiation_R : forall c e,
    instantiation c e ->
    forall x t T,
      lookup x c = Some T ->
      lookup x e = Some t -> R T t.
Proof.
  intros c e V. induction V; intros x' t' T' G E.
    solve_by_invert.
    unfold lookup in *.  destruct (String.eqb x x').
      inversion G; inversion E; subst.  auto.
      eauto.
Qed.

Lemma instantiation_drop : forall c env,
    instantiation c env ->
    forall x, instantiation (drop x c) (drop x env).
Proof.
  intros c e V. induction V.
    intros.  simpl.  constructor.
    intros. unfold drop.
    destruct (String.eqb x x0); auto. constructor; eauto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Congruence Lemmas on Multistep *)

(** We'll need just a few of these; add them as the demand arises. *)

Lemma multistep_App2 : forall v t t',
  value v -> (t -->* t') -> <{ v t }> -->* <{ v t' }>.
Proof.
  intros v t t' V STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_App2; eauto.  auto.
Qed.

(* FILL IN HERE *)

(* ----------------------------------------------------------------- *)
(** *** The R Lemma *)

(** We can finally put everything together.

    The key lemma about preservation of typing under substitution can
    be lifted to multi-substitutions: *)

Lemma msubstTCA_preserves_kinding : forall c e,
     instantiation c e ->
     forall Delta ty K, (mupdate Delta c) |-* ty : K ->
     Delta |-* (msubstTCA e ty) : K.
Proof.
    intros c e H. induction H; intros.
    simpl in H. simpl. auto.
    simpl in H2.  simpl.
    apply IHinstantiation.
    eapply substituteTCA_preserves_kinding; eauto.
    assert ([] |-* v : T) by apply (R_typable_empty H0).
    apply Kinding.weakening_empty.
    assumption.
Qed.

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
Admitted.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
Admitted.

(* TODO: Should be true (but is it in small step??? ) *)
(* We could add hypothesis value v, but I don't know if we need it*)
(* Lemma step_substitution : forall X s v T,
  s -->* v -> substituteTCA X s T -->* substituteTCA X v T.
Proof.
  intros X s v T hstep.
  induction T.
  - funelim (substituteTCA X s (Ty_Var t)); try discriminate.
    inversion H.
    destruct (eqb_spec X Y).
    + rewrite <- Heqcall.
      subst.
      rewrite subst_tyvar_value.
      assumption.
    + subst.
      rewrite subst_tyvar_identity; [|assumption].
      rewrite subst_tyvar_identity; [|assumption].
      apply multi_refl.
  - shelve.
  - shelve.
  - shelve.
  - shelve.
  - rewrite substTCA_abs.
    rewrite substTCA_abs.
    destruct (eqb_spec X b).
    + apply multi_refl.
    +  


Admitted.

Lemma multistep_substitution : forall X s v T env,
  s -->* v -> msubstTCA ((X, s)::env) T -->* msubstTCA ((X, v)::env) T.
Proof.
  intros X s v T env0 Hstep.
  induction T.
Admitted. *)

(** And at long last, the main lemma. *)

Lemma msubstTCA_R : forall c env ty K,
    c |-* ty : K ->
    instantiation c env ->
    R K (msubstTCA env ty).
Proof.
  intros c env0 ty K HT V.
  generalize dependent env0.
  (* We need to generalize the hypothesis a bit before setting up the induction. *)
  remember c as Delta.
  generalize dependent c.
  induction HT; intros.

  - (* T_Var *)
   destruct (instantiation_domains_match V H) as [t P].
   eapply instantiation_R; eauto.
   rewrite msubstTCA_var.  rewrite P. auto. eapply instantiation_env_closed; eauto.
  - shelve.
  - shelve.
  - shelve.
  - shelve.
  - (* T_Abs *)
    unfold R. fold R. split; [|split].
    + apply msubstTCA_preserves_kinding with (c := Δ ); [assumption|].
      unfold mupdate. 
      rewrite app_nil_r.
      apply K_Lam.
      assumption.
    + apply value_halts.
      rewrite msubstTCA_abs. (* TODO: probably we don't even need something that strong?*)
      apply v_abs. (* NOTE: this will change when we normalise under the lambda*)
    + 
     intros.
     destruct (R_halts H) as [v [P Q]].
     pose proof (multistep_preserves_R _ _ _ P H).
     apply multistep_preserves_R' with (t' := msubstTCA ((X, v)::env0) T).
     (* * apply multistep_preserves_R' with (t' := msubstTCA ((X, v)::env0) T). *)
     * 
       apply K_App with (K1 := K1).
       -- apply msubstTCA_preserves_kinding with (c := Δ).
        ++ assumption.
        ++ unfold mupdate. rewrite app_nil_r.
           apply K_Lam.
           assumption.
       -- induction K1; unfold R in H; destruct H as [H _]; assumption.  
     * 
       simpl.
       rewrite subst_msubstTCA.
       -- rewrite msubstTCA_abs.
          apply multi_trans with (y := (Ty_App (Ty_Lam X K1 (msubstTCA (drop X env0) T)) v)).
          ++ apply multistep_App2; [|assumption].
             apply v_abs. (* NOTE May get more difficult if lambda is no longer a value*)
          ++ apply multi_R.
             apply ST_AppAbs.
             assumption.
          
       -- induction K1; unfold R in H0; destruct H0 as [H0 _];
          apply typable_empty__closed in H0;
          assumption.
       -- apply instantiation_env_closed in V.
          assumption.
     * apply multistep_preserves_R' with (t' := msubstTCA ((X, v) :: env0) T).
       -- apply msubstTCA_preserves_kinding with (c := ((X, K1)::Δ)).
          ++ apply V_cons; assumption.
             
          ++ unfold mupdate. rewrite app_nil_r.
             assumption.
       -- apply multi_refl. 
       -- apply IHHT with (c:= ((X, K1)::Δ)); [reflexivity|].
          apply V_cons; assumption.
       
  - (* T_App *)
    rewrite msubstTCA_app.
    destruct (IHHT1 c HeqDelta env0 V) as [_ [_ P1]].
    pose proof (IHHT2 c HeqDelta env0 V) as P2.
    fold R in P1. auto.
Admitted.

(* ----------------------------------------------------------------- *)
(** *** Normalization Theorem *)

(** And the final theorem: *)

Theorem normalization : forall ty K, [] |-* ty : K -> halts ty.
Proof.
  intros.
  replace ty with (msubstTCA nil ty) by reflexivity.
  apply (@R_halts K).
  apply (msubstTCA_R nil); eauto.
  eapply V_nil.
Qed.

(* 2024-01-02 21:54 *)


