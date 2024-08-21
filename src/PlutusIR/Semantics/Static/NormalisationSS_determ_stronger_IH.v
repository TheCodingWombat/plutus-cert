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

(* In the STLC from PLF, we did not have that Ty_App could be a normal value, why do we need it now? *)
(* Now Ty_App (Ty_Var x) (Ty_Var y) is a value because x is neutral, and y is neutral thus a value *)
Inductive value : ty -> Prop :=
  | v_neutral : forall ty1,
      neutral ty1 ->
      value ty1
  | v_abs : forall x K2 ty1,
      value ty1 ->
      value <{\x:K2, ty1}>
  | v_builtin : forall st,
      value (Ty_Builtin st)
      
  with neutral : ty -> Prop :=
  | ne_var : forall x,
      neutral (Ty_Var x) (* TODO, notation for tyvars?*)
  | ne_app : forall ty1 ty2,
      neutral ty1 ->
      value ty2 ->
      neutral (Ty_App ty1 ty2).


Hint Constructors value : core.

Reserved Notation "ty '-->' ty'" (at level 40).

Definition not_tylam (t : ty) : Prop :=
  match t with
  | Ty_Lam _ _ _  => False
  | _ => True
  end.

(* lambdas are no longer values unless their bodies are values*)
(*  So we will start normalising the body*)
Inductive step : ty -> ty -> Prop :=
  | ST_Abs : forall ty1 ty1' x K2,
      ty1 --> ty1' ->
      <{(\x:K2, ty1)}> --> <{(\x:K2, ty1')}>
  | ST_AppAbs : forall x K2 v1 v2,
         value v1 -> (* Problematic *)
         value v2 -> 
         <{(\x:K2, v1) v2}> --> <{ [x:=v2]v1 }>
  | ST_App1 : forall ty1 ty1' ty2,
         ty1 --> ty1' ->
         <{ty1 ty2}> --> <{ty1' ty2}>
  | ST_App2 : forall v1 ty2 ty2',
         value v1 ->
         ty2 --> ty2' ->
         <{v1 ty2}> --> <{v1 ty2'}>

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


Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
   not (exists t', R t t').

Notation step_normal_form := (normal_form step).

Lemma value__normal : forall t, value t -> step_normal_form t.
Proof with eauto.
  (* intros t H.
  induction H; intros [t' Hstep].
  unfold step_normal_form in IHvalue.
  unfold not in IHvalue.
  apply IHvalue.
  inversion Hstep.
  exists ty1'.
  assumption.
  inversion Hstep.  *)
Admitted.

(* Shouldnt be for all K, only for the K matching T*)
Lemma confluence_helper : forall y t1 t1' t2,
  t1 --> t1' -> substituteTCA y t2 t1 -->* substituteTCA y t2 t1'.
Proof.
  intros y t1 t1' t2 IHt1step.
  induction IHt1step.
  - admit. (* lam reduction, should be doable, casing on X=?x*)
  - admit. (* Uhm, I don't know how renaming works *) 
  - admit. (* Should be easy by applying subst on TyApp*)
  - admit. (* Same *)
Admitted.

Theorem confluence : forall x y y' z : ty,
  x --> y -> x --> y' -> exists z, y -->* z /\ y' --> z.
Proof.
Admitted.

(* ----------------------------------------------------------------- *)
(** *** Preservation *)

Theorem step_preserves_kinding : forall t t' Gamma K,
   Gamma |-* t : K  ->
   t --> t'  ->
   Gamma |-* t' : K.
Proof with eauto.
(* intros t t' Gamma K HT. generalize dependent t'.
(* remember [] as Gamma. *)
induction HT; intros t' HE; subst; inversion HE; subst... 
- apply K_Lam.
  apply IHHT. assumption.  
- apply substituteTCA_preserves_kinding with K1...
  inversion HT1...
- (* T_App *)
  inversion HE; subst...
  + (* ST_AppAbs *)
    apply substituteTCA_preserves_kinding with K1...
    inversion HT1...
  + apply K_App with (K1 := K1). 
    * specialize IHHT1 with (ty1'). 
      apply IHHT1. assumption.
    * assumption. 
  + apply K_App with (K1 := K1); assumption. 
- apply K_App with (K1 := K1); [assumption|].
  apply IHHT2.
  assumption.     *)
Admitted. (* Works, only admitted to speed up Coq*)

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
        appears_free_in x <{ \y : T11, t12 }> (* TODO: fresh/renaming issues?*)
.

Hint Constructors appears_free_in : core.

Definition closed (t:ty) :=
  forall x, ~ appears_free_in x t.

Lemma context_invariance : forall Gamma Gamma' t K,
     Gamma |-* t : K  ->
     (forall x, appears_free_in x t -> List.lookup x Gamma = List.lookup x Gamma')  ->
     Gamma' |-* t : K.
Proof.
  (* intros.
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
      auto.  *)
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
   (* induction E1; intros t'' E2; inversion E2; subst; clear E2. *)
   induction E1; intros t'' E2; inversion E2; subst; clear E2;
   try solve_by_invert; try f_equal; try solve_by_value_nf; eauto.   
Admitted.


Definition halts  (t:ty) : Prop :=  exists t', t -->* t' /\  value t'.

(* Is this useful? *)
(* There is some useful struture here. Since we are deterministic, subst t and subst t'
   approach s' from the same linear path. So there must be two options:
   substituteTCA X t s -->* substituteTCA X t' s
   or
   substituteTCA X t' s -->* substituteTCA X t s

  Is that useful? Maybe it is enough, or maybe we can even discriminate the last case?
*)
Lemma subst_preserves_step2 : forall X t t' s,
  t --> t' -> halts (substituteTCA X t s) -> exists s', substituteTCA X t s -->* s' /\ substituteTCA X t' s -->* s'.
Proof.
  intros X t t' s Hstep Hhalts.
  induction s.
  - admit.
  - shelve.
  - shelve.
  - shelve.
  - shelve.
  - admit. (* I think easier. Assume s' = substituteTCA X t' s, then multi_refl for the second case*)
  - assert (halts (substituteTCA X t s1)) by admit.
    remember H as H'; clear HeqH'.
    destruct H as [Hv H].
    apply IHs1 in H'.
    destruct H' as [s'H [s1tStep s1t'Step]].
    assert (value s'H) by admit.
    exists (Ty_App (s'H) (substituteTCA X t' s2)).
    split.
    (* By non-determinism, we have that s1 and s2 will both reduce to a value, since the whole is halting
       so, this works out.*)
Admitted.

(* TODO: Substitution step lemma needed *)
Lemma subst_preserves_step : forall X t t' v',
  t --> t' -> value v' -> substituteTCA X v' t  -->* substituteTCA X v' t'.
Proof.
  intros X t t' v H H_value_v'.
  generalize dependent t.
  induction t'.
  induction t; intros t' Hstep; inversion Hstep.
  - intros.
    assert (value ty1') by admit.
    admit. (* pull subst into lambda. If X==b, then show t -->* ty1', otherwise show subst t -->* subst ty1'*)
  - admit. (* uhm, since t2 and \x:K2,v1 are already values, IHt1 and IHt2 don't tell us anything*)
  (* Update: With new deterministic small step semantics this works*)
  (* Back to the old one: Even with the above lemma step2, it still reduces to *)
  - intros H. (* Impossible with not_tylam deterministic semantics*)
    admit. (* pull subst in, extend ST_App1 to multistep, use IHt1
      (* TO use IHt1, we need to use v = ty1'.
          t1 --> ty1' check
          value ty1': PROOF: We have value ty1' t2
            from that we know that is it by the ne_abs constructor, so we know ty1' neutral
            by v_neutral, we know every neutral term is also normal *)*)  
  - admit. (* Same as above *)
  - admit.
  - admit.
  - admit.
  - intros t Hstep. inversion Hstep. 
Admitted.

(** A trivial fact: *)

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros v H. unfold halts.
  exists v. split.
  - apply multi_refl.
  - assumption.
Qed.

Fixpoint R (T:kind) (t : ty) : Prop :=
  ([] |-* t : T /\ halts t /\ 
  (match T with
   | <{ * }>  => True
   | <{ K1 -> K2 }> => (forall s : ty, R K1 s -> R K2 <{t s}> ) (* For ty constr we needed value s here I think.*)
   end)).

(** As immediate consequences of this definition, we have that every
    element of every set [R_T] halts in a value and is closed with type
    [T] :*)

Lemma R_halts : forall {T} {t}, R T t -> halts t.
Proof.
  (* intros.
  destruct T; unfold R in H; destruct H as [v [H [Hhalts _]]]; 
  unfold halts; exists v; assumption. *)
Admitted.

Lemma R_types : forall K T,
  R K T -> [] |-* T : K.
Proof.
Admitted.

Lemma R_typable_empty : forall {T} {t}, R T t -> [] |-* t : T.
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [v [H _]]; assumption.
Qed.

Corollary R_ty_closed : forall K T,
  R K T -> closed T.
Proof.
Admitted.

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
Qed. (* Works with deterministic Small step semantics*)

(** Now the main lemma, which comes in two parts, one for each
    direction.  Each proceeds by induction on the structure of the type
    [T]. In fact, this is where we make fundamental use of the
    structure of types.

    One requirement for staying in [R_T] is to stay in type [T]. In the
    forward direction, we get this from ordinary type Preservation. *)

Lemma step_preserves_R : forall T t t', (t --> t') -> R T t -> R T t'.
Proof.
 induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [HKind [halts_t RRt]].
  (* Bool *)
  - split. eapply step_preserves_kinding; eauto.
    split; eauto.
    rewrite step_preserves_halting with (t' := t') in halts_t; assumption.
  - split. eapply step_preserves_kinding; eauto.
    split; eauto. (* TODO: Understand why we don't have todo the forall R s -> R (v s), it seems to already be in the assumptions*)
    rewrite step_preserves_halting with (t' := t') in halts_t; assumption.
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
  induction K; intros t t' E Rt; unfold R; fold R; intros H; destruct H as [v H].
  - admit.
  - split. assumption.
    split. admit.
     
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
Admitted. 

Lemma multistep_preserves_R' : forall T t t',
  [] |-* t : T -> (t -->* t') -> R T t' -> R T t.
Proof.
  intros T t t' HT STM.
  induction STM; intros.
    assumption.
    eapply step_preserves_R'.  assumption. apply H. apply IHSTM.
    eapply step_preserves_kinding;  eauto. auto.
Qed.

(* Is this true, and if so, can this be useful?
Lemma step_preserves_R'2 : forall T t t' (s : ty),
  [] |-* t : T -> (t -->* s) -> (t' -->* s) -> R T t' -> R T t.
Proof.
  intros T t t' s HT HSt HSt'.
  apply multistep_preserves_R'.
  - assumption.
  - 

Admitted. *)


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

(** Closed environments are those that contain only closed terms. *)

Fixpoint closed_env (env:env) :=
  match env with
  | nil => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.

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
  (* unfold closed, not.
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
     shelve. (* TODO: Check if new lambda normalising body is an issue here, but I don't think this uses step*)
     
    - (* app *)
      funelim (substituteTCA x v <{t1 t2}>); try discriminate.
      rewrite <- Heqcall in A.
      inversion A.
      + apply IHt1 with (x := X) (v := U); [apply P | ].
        inversion H1.
        subst...
      + apply IHt2 with (x := X) (v := U); [apply P | ].
        inversion H1.
        subst...      *)
Admitted.

Lemma duplicate_subst : forall t' x t v,
  closed v -> <{ [x:=t]([x:=v]t') }> = <{ [x:=v]t' }>.
Proof.
  intros. eapply vacuous_substitution. apply subst_not_afi. assumption.
Qed.

Lemma drop_duplicate_msubst : forall X T v env,
  closed v -> closed_env env -> msubstTCA ((X, v)::env) T = msubstTCA ((X, v)::(drop X env)) T.
Proof.
Admitted.

Lemma subst_tyvar_identity : forall x v t,
  x <> t -> <{[x := v] {t}}> = <{{t}}>.
Proof.
  (* intros x v t Hneq.
  funelim (substituteTCA x v (Ty_Var t)); try discriminate.
  inversion H.
  rewrite <- H1 in Hneq.
  apply eqb_neq in Hneq.
  rewrite Hneq in Heqcall.
  rewrite <- Heqcall.
  rewrite -> H1.
  reflexivity. *)
Qed.

Lemma subst_tyvar_value : forall x v ,
  <{[x := v] {x}}> = <{v}>.
Proof.
  (* intros x v.
  funelim (substituteTCA x v (Ty_Var x)); try discriminate.
  inversion H.
  rewrite H1 in Heqcall.
  rewrite eqb_refl in Heqcall.
  rewrite <- Heqcall.
  reflexivity. *)
Qed.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v -> closed v1 ->
    <{ [x1:=v1]([x:=v]t) }> = <{ [x:=v]([x1:=v1]t) }>.
Proof with eauto.
 (* induction t; intros; simpl.
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
  - shelve. *)
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
  (* induction ss; intros; [reflexivity|].
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
    rewrite IHss; [reflexivity|assumption].  *)
Admitted.


(* TODO: This is not true because of renaming, but I don't think it will change the proofs using it*)
(* Should not be influenced by changing lambda body normalisation*)
Lemma msubstTCA_abs: forall ss x T t,
  msubstTCA ss <{ \ x : T, t }> = Ty_Lam x T (msubstTCA (drop x ss) t).
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. destruct (String.eqb s x); simpl; auto.
Admitted.


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
  (t -->* t') -> <{ v t }> -->* <{ v t' }>.
Proof.
  intros t t' V STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_App2; eauto.  auto.
Qed.

Lemma multistep_AppAbs : forall X K T v,
  Ty_App (Ty_Lam X K T) v -->* substituteTCA X v T.
Proof.
Admitted.

Lemma multistep_Abs : forall t t' X K,
  t -->* t' -> Ty_Lam X K t -->* Ty_Lam X K t'.
Proof.
Admitted.

(* FILL IN HERE *)

(* ----------------------------------------------------------------- *)
(** *** The R Lemma *)

(* Lemma R_distributes_over_appr : ,
  R K (Ty_App v1 v2) -> R K v2. *)

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

(* DOES NOT DEPEND ON DETERMINISM *)
Lemma existsence_ty_R : forall K,
  exists v, value v /\ R K v.
Proof.
  (* intros K.
  induction K.
  - exists (Ty_Builtin DefaultUniInteger).
    split.
    + apply v_builtin.
    + unfold R.
      split; [|split].
      * apply K_Builtin.
        apply K_DefaultUniInteger.
      * unfold halts.
        exists (Ty_Builtin DefaultUniInteger).
        split. 
        -- apply multi_refl.
        -- apply v_builtin.
      * reflexivity.
  - destruct IHK1 as [ty1 H1].
    destruct IHK2 as [ty2 H2].
    exists (Ty_Lam "x" K1 ty2). (* MEETING: Maybe we need to make "x" so that x not in anything, i.e. fresh. NOt possible I think, needs to work for arbitrary ty2?*)
    split.
    + apply v_abs.
      destruct H2.
      assumption.
    + unfold R; fold R; split; [|split]. (* TODO ask, shouldn't we get an induction hypothesis here?*)
      * apply K_Lam.
        destruct H2.
        destruct H1 as [_ H1].
        induction K2; unfold R in H0; destruct H0 as [H0 _]; 
          apply Kinding.weakening_empty; assumption.
      * unfold halts.
        (* TODO: We can construct 'x' as not being in ty2*)
        exists (Ty_Lam "x" K1 ty2).
        split.
        apply multi_refl.
        apply v_abs. destruct H2 as [H2 _].
        assumption.
      * intros ty' Hty'.
        (* under assumptions ty2 value and ty' value
          we can R step to having to show R K2 ty2[x = ty']*)
          (* Then under assumption x not in ty2, we can write out the subst by removing it
          So we have to show R K2 ty2. Assumption.*)
        destruct H2 as [H2norm H2R].
        remember H2R as H2R'; clear HeqH2R'.
        apply R_ty_closed in H2R.
        apply step_preserves_R' with (t' := substituteTCA "x" ty' ty2).
        -- apply R_types in Hty'.
           apply R_types in H2R'.
           apply K_App with (K1 := K1); [|assumption].
           apply K_Lam.
           apply Kinding.weakening_empty.
           assumption.

        -- apply ST_AppAbs.
           ++ assumption.
           ++ destruct H1 as [H1 _].
              assumption. 
        -- rewrite subst_closed; assumption. *)
Admitted.

(** And at long last, the main lemma. *)

(* Idea: Jacco's idea, but still one substitution! deosnt make sense?*)
(* Idea: Jacco's LR, but with gamma also in the t s case*)

Definition env_subset (env' env : list (string * ty)) : Prop :=
  True.


(* We had two ideas, and both are flawed for the APP case
   We cannot say that we know T1 T2 -->* v, because IHs say T1 and T2 to values, but nothing about their product*)
(* Solution would be to say that forall subsets env' of env0 that R K1 (msubstTCA env' v), but that is flawed in
   that the contexts are not empty.*)
Lemma msubstTCA_R' : forall c env ty K,
    c |-* ty : K ->
    instantiation c env ->
    exists v, msubstTCA env ty -->* v /\ value v /\
    R K v.
Proof.
 intros c env0 ty K HT V.
  generalize dependent env0.
  remember c as Delta.
  generalize dependent c.
  induction HT; intros.

  - (* T_Var *)
   destruct (instantiation_domains_match V H) as [t P].
   exists (Ty_Var X).
   
   split; [|split].
   
   + admit. (* lookup X in env0 => t, so substitute env0 in Ty_Var X, will become t, so t == t, so multi_refl*)
   + admit. (* t in env0 and env0 in instantiation, so a value*)
   + eapply instantiation_R; eauto.
   (* rewrite msubstTCA_var.  rewrite P. auto. eapply instantiation_env_closed; eauto. *)
   admit.
    
  - shelve.
  - shelve.
  - shelve.
  - shelve.
  - (* T_Abs *)

    assert (Henv0 : exists X_K1_v, instantiation ((X, K1) :: Δ) ((X, X_K1_v) :: env0)).
    {
      pose proof (existsence_ty_R K1) as existsv.
      destruct existsv as [v [valueV Rv]].
      exists v.
      apply V_cons; assumption.
    }
    destruct Henv0 as [X_K1_v Henv0].
    remember Henv0 as Henv0instants; clear HeqHenv0instants.
    specialize (IHHT ((X, K1)::Δ)).
    apply IHHT in Henv0; [|reflexivity].
    destruct Henv0 as [v_t Henv0].
    exists (Ty_Lam X K1 v_t).
    split; [admit|split; [admit|]].
    

    (* destruct Henv0 as [v Henv0]. *)
    (* exists (Ty_Lam X K1 v).
    split; [|split].
    {
      destruct Henv0 as [Henv0step Henv0].
      assert (halts (msubstTCA (drop X env0) T)) by admit.
      (* apply msubstTCA_abs *)
      (* IH: delta+X T -->* v, then by halts_preserves_msubst: delta-X T -->* v', so Ty_Lam  X (delta - X) T -->* Ty_Lam X v'*)
      admit. (* problematic! halts_preserves_msubst could give a different v*)

    }
    {
      admit.
      (* value Ty_Lam X v', because value v', because value v by IH *) 
    } *)
    (* admit. 
    admit. *)
    unfold R. fold R.  split; [|split].
    +
      (* apply msubstTCA_preserves_kinding with (c := Δ ); [assumption|]. *)
      (* unfold mupdate.  *)
      (* rewrite app_nil_r. *)
      apply K_Lam.
      (* By R K2 v we have [] |-* v : K2, so weakening gives result!*)
      admit.
    + (* Most problematic. How did Jacco fix this?*) admit. (* By value v, also value Ty_Lam v, so halts *)
    (* rewrite msubstTCA_abs. 
    
      specialize (IHHT ((X, K1)::Δ)).
      apply IHHT in Henv0; [|reflexivity].
      apply R_halts in Henv0.
      assert (halts (msubstTCA (drop X env0) T)).
      {
        rewrite drop_duplicate_msubst in Henv0.
        - apply halts_preserves_weaken_msubstTCA in Henv0.
          assumption.
        - apply instantiation_R with (x := X) (t := v) (T := K1) in Henv0'.
          + induction K1; unfold R; fold R; destruct Henv0' as [Henv0' _].
            * apply typable_empty__closed with (T := Kind_Base). assumption.
            * apply typable_empty__closed with (T := Kind_Arrow K1_1 K1_2). assumption.
          + simpl. rewrite eqb_refl. reflexivity.
          + simpl. rewrite eqb_refl. reflexivity.
        - apply instantiation_env_closed in V.
          assumption.  
           
      }
      unfold halts.
      destruct H.
      exists (Ty_Lam X K1 x).
      split; destruct H as [Hstep Hvalue].
      * apply multistep_Abs. assumption. 
      * apply v_abs.
        assumption. *)

    + (* This case makes no weird assumptions anymore, but it only works because of losing determinism*)
     intros.
     (* destruct (R_halts H) as [v [P Q]].
     pose proof (multistep_preserves_R _ _ _ P H). *)

     destruct (R_halts H) as [v_s [P Q]].
     pose proof (multistep_preserves_R _ _ _ P H).

     (* apply multistep_preserves_R' with (t' := (msubstTCA (env0) (substituteTCA X v_s v))).      *)
     apply multistep_preserves_R' with (t' := substituteTCA X v_s v).     
     * admit. (* should be true lol*) 
       (* apply K_App with (K1 := K1).
       -- apply msubstTCA_preserves_kinding with (c := Δ).
        ++ assumption.
        ++ unfold mupdate. rewrite app_nil_r.
           apply K_Lam.
           assumption.
       -- induction K1; unfold R in H; destruct H as [H _]; assumption.   *)
     * admit. (* by simple reductions from non-deterministic blablabla*) 
       (* simpl.
       rewrite msubstTCA_abs.
       (* TODO: we are fighting coq here, we should find out how to do this without all the asserts*)
       apply multi_trans with (y := (Ty_App (Ty_Lam X K1 (msubstTCA (drop X env0) T)) v)).
       {
        apply multistep_App2.
        assumption.

       }
       apply multi_trans with (y:= substituteTCA X v (msubstTCA (drop X env0) T)).
       {
        apply multistep_AppAbs.
       }
       rewrite subst_msubstTCA.
       -- apply multi_refl.
       -- induction K1; unfold R; fold R; destruct H0 as [H0 _]; 
          apply typable_empty__closed in H0; assumption.
       -- apply instantiation_env_closed in V; assumption.     *)
     *
      admit. (* By R K2 v, we have closed v, so no free X in v, so [X := v_s] v = v*)
      (* assert (msubstTCA env0 (substituteTCA X v T) = msubstTCA ((X, v)::env0) T).
      {
        simpl.
        reflexivity.
      }
      rewrite H1.
      assert (instantiation ((X, K1)::Δ) ((X, v)::env0)).
      { apply V_cons; assumption. }
      specialize (IHHT ((X, K1) :: Δ)).
      apply IHHT in H2.
      assumption.
      reflexivity. *)
       
  - (* T_App *)
    rewrite msubstTCA_app.
    destruct (IHHT1 c HeqDelta env0 V) as [_ [_ P1]].
    pose proof (IHHT2 c HeqDelta env0 V) as P2.
    fold R in P1. auto.

Lemma msubstTCA_R : forall c env ty K,
    c |-* ty : K ->
    instantiation c env ->
    R K (msubstTCA env ty).
Proof.
  intros c env0 ty K HT V.
  generalize dependent env0.
  remember c as Delta.
  generalize dependent c.
  induction HT; intros.

  - (* T_Var *)
   destruct (instantiation_domains_match V H) as [t P].
   
   split; [|split].
   
   + admit. (* lookup X in env0 => t, so substitute env0 in Ty_Var X, will become t, so t == t, so multi_refl*)
   + admit. (* t in env0 and env0 in instantiation, so a value*)
   + eapply instantiation_R; eauto.
   (* rewrite msubstTCA_var.  rewrite P. auto. eapply instantiation_env_closed; eauto. *)
    
  - shelve.
  - shelve.
  - shelve.
  - shelve.
  - (* T_Abs *)
    assert (Henv0 : exists X_K1_v, instantiation ((X, K1) :: Δ) ((X, X_K1_v) :: env0)).
    {
      pose proof (existsence_ty_R K1) as existsv.
      destruct existsv as [v [valueV Rv]].
      exists v.
      apply V_cons; assumption.
    }
    destruct Henv0 as [X_K1_v Henv0].
    remember Henv0 as Henv0instants; clear HeqHenv0instants.
    specialize (IHHT ((X, K1)::Δ)).
    apply IHHT in Henv0; [|reflexivity].
    (* destruct Henv0 as [v Henv0]. *)
    (* exists (Ty_Lam X K1 v).
    split; [|split].
    {
      destruct Henv0 as [Henv0step Henv0].
      assert (halts (msubstTCA (drop X env0) T)) by admit.
      (* apply msubstTCA_abs *)
      (* IH: delta+X T -->* v, then by halts_preserves_msubst: delta-X T -->* v', so Ty_Lam  X (delta - X) T -->* Ty_Lam X v'*)
      admit. (* problematic! halts_preserves_msubst could give a different v*)

    }
    {
      admit.
      (* value Ty_Lam X v', because value v', because value v by IH *) 
    } *)
    (* admit. 
    admit. *)
    unfold R. fold R.  split; [|split].
    +
      (* apply msubstTCA_preserves_kinding with (c := Δ ); [assumption|]. *)
      (* unfold mupdate.  *)
      (* rewrite app_nil_r. *)
      apply K_Lam.
      (* By R K2 v we have [] |-* v : K2, so weakening gives result!*)
      admit.
    + admit. (* By value v, also value Ty_Lam v, so halts *)
    (* rewrite msubstTCA_abs. 
    
      specialize (IHHT ((X, K1)::Δ)).
      apply IHHT in Henv0; [|reflexivity].
      apply R_halts in Henv0.
      assert (halts (msubstTCA (drop X env0) T)).
      {
        rewrite drop_duplicate_msubst in Henv0.
        - apply halts_preserves_weaken_msubstTCA in Henv0.
          assumption.
        - apply instantiation_R with (x := X) (t := v) (T := K1) in Henv0'.
          + induction K1; unfold R; fold R; destruct Henv0' as [Henv0' _].
            * apply typable_empty__closed with (T := Kind_Base). assumption.
            * apply typable_empty__closed with (T := Kind_Arrow K1_1 K1_2). assumption.
          + simpl. rewrite eqb_refl. reflexivity.
          + simpl. rewrite eqb_refl. reflexivity.
        - apply instantiation_env_closed in V.
          assumption.  
           
      }
      unfold halts.
      destruct H.
      exists (Ty_Lam X K1 x).
      split; destruct H as [Hstep Hvalue].
      * apply multistep_Abs. assumption. 
      * apply v_abs.
        assumption. *)

    + (* This case makes no weird assumptions anymore, but it only works because of losing determinism*)
     intros.
     (* destruct (R_halts H) as [v [P Q]].
     pose proof (multistep_preserves_R _ _ _ P H). *)

     destruct (R_halts H) as [v_s [P Q]].
     pose proof (multistep_preserves_R _ _ _ P H).

     (* apply multistep_preserves_R' with (t' := (msubstTCA (env0) (substituteTCA X v_s v))).      *)
     apply multistep_preserves_R' with (t' := substituteTCA X v_s v).     
     * admit. (* should be true lol*) 
       (* apply K_App with (K1 := K1).
       -- apply msubstTCA_preserves_kinding with (c := Δ).
        ++ assumption.
        ++ unfold mupdate. rewrite app_nil_r.
           apply K_Lam.
           assumption.
       -- induction K1; unfold R in H; destruct H as [H _]; assumption.   *)
     * admit. (* by simple reductions from non-deterministic blablabla*) 
       (* simpl.
       rewrite msubstTCA_abs.
       (* TODO: we are fighting coq here, we should find out how to do this without all the asserts*)
       apply multi_trans with (y := (Ty_App (Ty_Lam X K1 (msubstTCA (drop X env0) T)) v)).
       {
        apply multistep_App2.
        assumption.

       }
       apply multi_trans with (y:= substituteTCA X v (msubstTCA (drop X env0) T)).
       {
        apply multistep_AppAbs.
       }
       rewrite subst_msubstTCA.
       -- apply multi_refl.
       -- induction K1; unfold R; fold R; destruct H0 as [H0 _]; 
          apply typable_empty__closed in H0; assumption.
       -- apply instantiation_env_closed in V; assumption.     *)
     *
      admit. (* By R K2 v, we have closed v, so no free X in v, so [X := v_s] v = v*)
      (* assert (msubstTCA env0 (substituteTCA X v T) = msubstTCA ((X, v)::env0) T).
      {
        simpl.
        reflexivity.
      }
      rewrite H1.
      assert (instantiation ((X, K1)::Δ) ((X, v)::env0)).
      { apply V_cons; assumption. }
      specialize (IHHT ((X, K1) :: Δ)).
      apply IHHT in H2.
      assumption.
      reflexivity. *)
       
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


