(* From Equations Require Import Equations.
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
  | v_var : forall x,
      neutral (Ty_Var x) (* TODO, notation for tyvars?*)
  | v_app : forall ty1 ty2,
      neutral ty1 ->
      value ty2 ->
      neutral (Ty_App ty1 ty2).


Hint Constructors value : core.

Reserved Notation "ty '-->' ty'" (at level 40).

(* lambdas are no longer values unless their bodies are values*)
(*  So we will start normalising the body*)
Inductive step : ty -> ty -> Prop :=
  | ST_Abs : forall ty1 ty1' x K2,
      ty1 --> ty1' ->
      <{(\x:K2, ty1)}> --> <{(\x:K2, ty1')}>
  | ST_AppAbs : forall x K2 v1 v2,
         value v2 ->
         value (Ty_Lam x K2 v1) -> (*Toegevoegd: Needed for determinism *)
         <{(\x:K2, v1) v2}> --> <{ [x:=v2]v1 }>
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

(* ----------------------------------------------------------------- *)
(** *** Preservation *)

Theorem preservation : forall t t' T,
   [] |-* t : T  ->
   t --> t'  ->
   [] |-* t' : T.
Proof with eauto.
(* intros t t' T HT. generalize dependent t'.
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
Admitted.

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
Qed.


Definition halts  (t:ty) : Prop :=  exists t', t -->* t' /\  value t'.

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
   | <{ K1 -> K2 }> => (forall s : ty, R K1 s -> R K2 <{t s}> )
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

Lemma R_typable_empty : forall {T} {t}, R T t -> [] |-* t : T.
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [v [H _]]; assumption.
Qed.

(* Shouldnt be for all K, only for the K matching T*)
Theorem R_preserves_value_substTCA : forall K X U T T',
  R K T -> value U -> T -->* T' -> 
    exists v', substituteTCA X U T -->* v' /\ substituteTCA X U T' -->* v'.
Proof.
  intros K X v' T T' HR Hv Hstep.
  funelim (substituteTCA X v' T); try inversion Hstep; try discriminate.

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
 (* intros t t' ST.  unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V]].
  destruct STM.
   + exfalso; apply value__normal in V; eauto.
   + rewrite (step_deterministic _ _ _ ST H). exists z. split; assumption.
 - (* <- *)
  intros [t'0 [STM V]].
  exists t'0. split; eauto.
  apply multi_step with (y := t'); assumption. *)
Admitted.

Lemma multistep_goes_through_step : forall (t t' v : ty),
  value v -> t --> t' -> t -->* v -> t' -->* v.
Proof.
  (* intros Hvalue t t' v Hstep Hmulti.
  induction Hmulti.
    + exfalso.
      apply (value__normal) in v.
      unfold step_normal_form in v.
      unfold not in v.
      apply v.
      exists t.
      assumption.
    + assert (t = y). 
      {
       rewrite (step_deterministic x t y); try assumption.
       reflexivity. 
      }
      subst...
      assumption. *)
Admitted.

(** Now the main lemma, which comes in two parts, one for each
    direction.  Each proceeds by induction on the structure of the type
    [T]. In fact, this is where we make fundamental use of the
    structure of types.

    One requirement for staying in [R_T] is to stay in type [T]. In the
    forward direction, we get this from ordinary type Preservation. *)

Lemma step_preserves_R : forall T t t', (t --> t') -> R T t -> R T t'.
Proof.
 (* induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t [HKind [halts_t RRt]]]; exists typable_empty_t.
  (* Bool *)
  - split. eapply preservation; eauto.
    split; eauto.
    destruct halts_t.
    split; [|assumption].
    apply (multistep_goes_through_step t); assumption.
  - split. eapply preservation; eauto.
    split; eauto. (* TODO: Understand why we don't have todo the forall R s -> R (v s), it seems to already be in the assumptions*)
    destruct halts_t.
    split; eauto.
    apply (multistep_goes_through_step t); assumption. *)
Admitted.


(** The generalization to multiple steps is trivial: *)

Lemma multistep_preserves_R : forall T t t',
  (t -->* t') -> R T t -> R T t'.
Proof.
  intros T t t' STM; induction STM; intros.
  assumption.
  apply IHSTM. eapply step_preserves_R. apply H. assumption.
Admitted.

(** In the reverse direction, we must add the fact that [t] has type
   [T] before stepping as an additional hypothesis. *)

Lemma step_preserves_R' : forall K t t',
  [] |-* t : K -> (t --> t') -> R K t' -> R K t.
Proof. (* This proof was not in software foundations *)
  (* induction K; intros t t' E Rt; unfold R; fold R; intros H; destruct H as [v H]; exists v.
  - admit.
  - split. admit.
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
        assumption. *)
Admitted. 

Lemma multistep_preserves_R' : forall T t t',
  [] |-* t : T -> (t -->* t') -> R T t' -> R T t.
Proof.
  intros T t t' HT STM.
  induction STM; intros.
    assumption.
    eapply step_preserves_R'.  assumption. apply H. apply IHSTM.
    eapply preservation;  eauto. auto.
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


(* This is not true because of renaming, but I think I can still kind of use it
Lemma substTCA_abs: forall X1 K1 X2 K2 T,
  substituteTCA X1 K1 (Ty_Lam X2 K2 T) =
    if X1 =? X2 then Ty_Lam X2 K2 T else Ty_Lam X2 K2 (substituteTCA X1 K1 T).
Proof.
Admitted. *)

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

Lemma multistep_Abs : forall t t' X K,
  t -->* t' -> Ty_Lam X K t -->* Ty_Lam X K t'.

(* Lemma multistep_App2' : forall t s s',
  (s -->* s') -> <{t s}> -->* <{t s'}>.
Proof.
  intros t s s' STM. induction STM.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; eauto.
    
Qed. *)

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
    exists v, msubstTCA env ty -->* v /\ R K? v. (* I think we want to say something like this*)
Proof.
  intros c env0 ty K HT V.
  generalize dependent env0.
  (* We need to generalize the hypothesis a bit before setting up the induction. *)
  remember c as Delta.
  generalize dependent c.
  induction HT; intros.

  - (* T_Var *)
    admit.
   (* destruct (instantiation_domains_match V H) as [t P].
   eapply instantiation_R; eauto.
   rewrite msubstTCA_var.  rewrite P. auto. eapply instantiation_env_closed; eauto. *)
  - shelve.
  - shelve.
  - shelve.
  - shelve.
  - (* T_Abs *)
       assert (exists v', value v' /\ R K1 v').
     {
      (* I think this v' can be constructed as in normalisation.v*)
      (* Proving v' is R K2 v' is impossible, because it may have free vars*)
      admit.
     }
     destruct H as [my_v [my_Hvalue my_HR] ].
     assert ([] |-* my_v : K1) by admit.

     specialize IHHT with (c:= ((X, K1)::Δ)).
     specialize IHHT with (env0:=((X, my_v)::env0)).
     assert (exists v, msubstTCA ((X, my_v)::env0) T -->* v /\ R K2 v) by admit.
     destruct H0 as [the_v [the_vstep the_vR]].
     exists (Ty_Lam X K1 the_v).
     rewrite msubstTCA_abs.


    unfold R. fold R. exists my_v.  split; [|split].
    + apply msubstTCA_preserves_kinding with (c := Δ ); [assumption|].
      unfold mupdate. 
      rewrite app_nil_r.
      apply K_Lam.
      assumption.
    + rewrite msubstTCA_abs. (* TODO: probably we don't even need something that strong?*)
      admit. (* NOTE: this will change when we normalise under the lambda*)
    + 
     intros.
     destruct (R_halts H) as [v [P Q]].
     pose proof (multistep_preserves_R _ _ _ P H).
     (* We should be able to prove something like a subset of this env0 T halting a la normalisation.v*)
     (* assert (exists v'_RK2, R K2 (msubstTCA ((X, v'_RK2)::env0) T)) by admit. (* By IHHT*)
     *)
     destruct H1 as [v' [H1step H1value]].
     
     
     (* Using v' here may solve the problem, but how do we get this v'?*)
     apply multistep_preserves_R' with (t' := substituteTCA X v v').
     
     (* apply multistep_preserves_R' with (t' := msubstTCA ((X, v)::env0) T). *)
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
       rewrite msubstTCA_abs.
       admit. (* SHould now be doable!*)
       (* apply multi_trans with (y := (Ty_App (Ty_Lam X K1 v') s)).
       -- assert ((Ty_Lam X K1 (msubstTCA (drop X env0) T)) -->* Ty_Lam X K1 v').
       {

        admit.

       }
       (* Hier 'ontstaat' het probleem al, dat we iets aan de rechterkant van de
           -->* hebben van de vorm [X := v] T, met T niet een value,
            daar is niet heen te steppen*) *)

     * (* We only moved the problem? From IHHT we can get
          R K2 [X := v] T', with T' = msubstTCA (drop X env0) T*) 
          apply step_preserves_R with (t := Ty_App (Ty_Lam X K1 v') v).
       apply ST_AppAbs; eauto.
       apply multistep_preserves_R with (t := Ty_App (Ty_Lam X K1 (msubstTCA (drop X env0) T)) v).
       admit.


      (* Below works without using v' construction, goal is then:
          R K2 (msubstTCA ((X, v) :: env0) T )*)
(*      
      apply multistep_preserves_R' with (t' := msubstTCA ((X, v) :: env0) T).
         
       -- 
          apply msubstTCA_preserves_kinding with (c := ((X,K1)::Δ)).
          ++ apply V_cons; assumption.
             ++ unfold mupdate. rewrite app_nil_r. assumption.

          
      
       -- simpl. apply multi_refl.
        
       -- apply IHHT with (c:= ((X, K1)::Δ)); [reflexivity|].
          apply V_cons; assumption. *)
       
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

 *)
