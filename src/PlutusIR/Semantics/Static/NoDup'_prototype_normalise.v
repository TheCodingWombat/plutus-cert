From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

From PlutusCert Require Import Util.List util.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.

Lemma empty_concat : forall (A : Type), (([] : list A) = [] ++ [])%list.
Proof.
  intros A. 
  simpl. reflexivity.
Qed.



(** kinds *)
Inductive kind :=
  | Kind_Base : kind
  | Kind_Arrow : kind -> kind -> kind.

(** Types *)
Inductive ty :=
  | Ty_Var : string -> ty
  | Ty_Lam : string -> kind -> ty -> ty
  | Ty_App : ty -> ty -> ty
.

(** Normal types *)
Inductive normal_Ty : ty -> Prop :=
  | NO_TyLam : forall bX K T,
      normal_Ty T ->
      normal_Ty (Ty_Lam bX K T)
  | NO_neutral : forall T,
      neutral_Ty T ->
      normal_Ty T

with neutral_Ty : ty -> Prop :=
  | NE_TyVar : forall X,
      neutral_Ty (Ty_Var X)
  | NE_TyApp : forall T1 T2,
      neutral_Ty T1 ->
      normal_Ty T2 ->
      neutral_Ty (Ty_App T1 T2).

(* Maybe instead: if T is well_kinded and an application, then there is no capture*)
(* Theorem well_kinded__no_capture2 Δ T1 T2 K :
    (Δ |-* (Ty_App T1 T2) : K) -> (In X (ftv T2)) -> (~ In X (btv T1)). *)
Fixpoint substituteT (X : string) (U T : ty) : ty :=
  match T with
  | Ty_Var Y =>
    if X =? Y then U else Ty_Var Y
  | Ty_Lam Y K1 T' =>
    if X =? Y then Ty_Lam Y K1 T' else Ty_Lam Y K1 (substituteT X U T')
  | Ty_App T1 T2 =>
    Ty_App (substituteT X U T1) (substituteT X U T2)
  end.

(** Type normalisation *)
Inductive normalise : ty -> ty -> Prop :=
  | N_BetaReduce : forall bX K T1 T2 T1n T2n T,
      normalise T1 (Ty_Lam bX K T1n) ->    
      normalise T2 T2n ->
      normalise (substituteT bX T2n T1n) T ->
      normalise (Ty_App T1 T2) T
  | N_TyApp : forall T1 T2 T1n T2n,
      normalise T1 T1n ->
      neutral_Ty T1n ->
      normalise T2 T2n ->
      normalise (Ty_App T1 T2) (Ty_App T1n T2n)
  | N_TyLam : forall bX K T0 T0n,
      normalise T0 T0n ->
      normalise (Ty_Lam bX K T0) (Ty_Lam bX K T0n)
  | N_TyVar : forall X,
      normalise (Ty_Var X) (Ty_Var X)
  .


Fixpoint kind_eq (K1 K2 : kind) : bool :=
    match K1, K2 with
    | Kind_Base, Kind_Base => true
    | Kind_Arrow K11 K12, Kind_Arrow K21 K22 =>
        if kind_eq K11 K21 then
            kind_eq K12 K22
        else false
    | _, _ => false
    end.

Fixpoint ty_eq (T1 T2 : ty) : bool :=
    match T1, T2 with
    | Ty_Var x1, Ty_Var x2 => if string_dec x1 x2 then true else false
    | Ty_Lam x1 K1 T1', Ty_Lam x2 K2 T2' =>
        if string_dec x1 x2 then
            if (kind_eq K1 K2) then
                ty_eq T1' T2'
            else false
        else false
    | Ty_App T11 T12, Ty_App T21 T22 =>
        if ty_eq T11 T21 then
            ty_eq T12 T22
        else false
    | _, _ => false
    end.

Fixpoint btv (T : ty) : (list string) :=
    match T with
    | Ty_Var x => []
    | Ty_Lam x K T0 => x :: (btv T0)
    | Ty_App T1 T2 => btv T1 ++ btv T2
    end.

Fixpoint ftv_ignore_lam (T : ty) : (list string) :=
    match T with
    | Ty_Var x => [x]
    | Ty_Lam x K T0 => [] (* Where we call this, we know there are no lams. *)
    | Ty_App T1 T2 => ftv_ignore_lam T1 ++ ftv_ignore_lam T2
    end.

Fixpoint drop_btv (Δ : list (string * kind)) (btvs : list string) : list (string * kind) :=
    match Δ with
    | ((X, K)::Δ') => 
                    if (in_dec string_dec X btvs) then
                        (drop_btv Δ' btvs)
                      else
                        ((X, K)::(drop_btv Δ' btvs))
    | nil => nil
    end.


Fixpoint lookup {X:Type} (k : string) (l : list (string * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if j =? k then Datatypes.Some x else lookup k l'
  end.

(* It may already be present, but only with the same body *)
Definition P_ND (X : string) (T : ty) (Δ : list (string * ty)) := 
  forall T', lookup X Δ = Some T' -> T = T'.

(* Not strong enough. Even when shadowed things have different T, it is a problem*)
Definition P_ND2 (Δ1 Δ2 : list (string * ty)) :=
    forall X T T', lookup X Δ1 = Some T -> lookup X Δ2 = Some T' -> T <> T' -> False.

Definition P_ND2' (Δ1 Δ2 : list (string * ty)) :=
    forall X T T', In (X, T) Δ1 -> In (X, T') Δ2 -> T = T'.

(* If a binder occurs multiple times, and we started with a GU term,
    we must have had a beta reduction. This we only do with normal types.
*)
Definition P_Dup_Normal (Δ1 Δ2 : list (string * ty)) :=
    forall X T T', In (X, T) Δ1 -> In (X, T') Δ2 -> T = T' -> normal_Ty T.

Definition P_BF (Δ : list (string * ty)) (Γ : list string) :=
    forall X, In X Γ -> ~ In X (map fst Δ).

(*
    Δ keeps track of lambda bodies, to make sure we never have dissimilar bodies for the same binder
    Γ keeps track of ftvs: no ftv may be bound somewhere else
*)
Reserved Notation "Δ : Γ '⊢' T" (at level 40, Γ at level 0, T at level 0, no associativity).
Inductive WK_Dup' : list (string * ty) -> list string -> ty -> Prop :=
  | ND_Var : forall Γ X,
      In X Γ ->
      [] : Γ ⊢ (Ty_Var X)   (* I changed this to nil, so that we cannot have random stuff in there*)
  | ND_Lam : forall Δ Γ X K1 T,
      Δ : (X::Γ) ⊢ T ->
      (* P_ND X T Δ ->  *)
      (* Do we need this? *)
      P_BF ((X, T)::Δ) Γ -> (* uhm *)
      ((X, T)::Δ) : Γ ⊢ (Ty_Lam X K1 T)
  | ND_App : forall Δ1 Δ2 Γ T1 T2 ,
      Δ1 : Γ ⊢ T1 ->
      Δ2 : Γ ⊢ T2 ->
      P_ND2' Δ1 Δ2 ->
      P_Dup_Normal Δ1 Δ2 ->
      P_BF (Δ1 ++ Δ2) Γ ->
      (Δ1 ++ Δ2) : Γ ⊢ (Ty_App T1 T2)
where "Δ : Γ '⊢' T" := (WK_Dup' Δ Γ T).


Create HintDb noDup_db.
Hint Constructors WK_Dup' : noDup_db.

Definition KB := Kind_Base.

(* 
(λX. λY. X Y)   (ΛY. Y)
*)
Definition t1_bad := Ty_App
        ( Ty_Lam "X" KB (Ty_Lam "Y" KB (Ty_App (Ty_Var "X") (Ty_Var "Y"))))
        (Ty_Lam "Y" KB (Ty_Var "Y")).

Lemma t1_bad__not_wk :
    forall Δ Γ,
        (Δ : Γ ⊢ t1_bad) -> False.
Proof.
    intros.
    unfold t1_bad in H.
    inversion H; subst; clear H.
    inversion H3; subst; clear H3.
    inversion H2; subst; clear H2.
    inversion H5; subst; clear H5.
    unfold P_ND2' in H4.
    specialize H4 with (X := "Y") (T := Ty_App (Ty_Var "X") (Ty_Var "Y"))
                (T' := (Ty_Var "Y")).
    discriminate H4; auto with *.
Qed.

(* 
(λW.  (λZ. W Z) (λY. Y))   (λX. λY. X Y)
This term multisteps to t1_bad *)
Definition t2_bad := Ty_App
        (Ty_Lam "W" KB (Ty_App 
                (Ty_Lam "Z" KB (Ty_App (Ty_Var "W") (Ty_Var "Z")))
                (Ty_Lam "Y" KB (Ty_Var "Y"))))
        (Ty_Lam "X" KB (Ty_Lam "Y" KB (Ty_App (Ty_Var "X") (Ty_Var "Y")))).

Lemma t2_bad__not_wk :
    forall Δ Γ,
        (Δ : Γ ⊢ t2_bad) -> False.
Proof.
    intros.
    unfold t2_bad in H.
    inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    inversion H3; subst; clear H3.
    inversion H5; subst; clear H5.
    inversion H6; subst; clear H6.
    inversion H2; subst; clear H2.
    unfold P_ND2' in H4.

    specialize H4 with (X := "Y") (T := (Ty_Var "Y")) (T' := (Ty_App (Ty_Var "X") (Ty_Var "Y"))).
    discriminate H4; auto with *.
Qed.

Definition t2_good := Ty_App
        (Ty_Lam "X" KB (Ty_App (Ty_Lam "Y" KB (Ty_App (Ty_Var "Y") (Ty_Var "X"))) (Ty_Lam "Z" KB (Ty_Var "X"))))
        (Ty_Lam "V" KB (Ty_Var "V")).

Lemma t2_good__wk :
    exists Δ,
        (Δ : nil ⊢ t2_good).
Proof with eauto with noDup_db.
    exists (
            (
             ("X", (Ty_App (Ty_Lam "Y" KB (Ty_App (Ty_Var "Y") (Ty_Var "X"))) (Ty_Lam "Z" KB (Ty_Var "X"))))
            ::([("Y", (Ty_App (Ty_Var "Y") (Ty_Var "X")))]
            ++ ("Z", (Ty_Var "X"))::nil))
            ++
            [("V", (Ty_Var "V"))])%list.
    unfold t2_good.
    apply ND_App.
    - apply ND_Lam.
      apply ND_App.
      apply ND_Lam.
      rewrite empty_concat.
      constructor.
      constructor. apply in_eq. constructor. apply in_cons. apply in_eq.
      
      unfold P_ND2'. intros. inversion H.
      unfold P_Dup_Normal. intros. inversion H.
      unfold P_BF. intros. intros Hcontra. simpl in Hcontra. assumption.
      unfold P_BF. intros. inversion H. subst. simpl. intuition. congruence. inversion H0.
      apply ND_Lam.
      constructor. apply in_cons. apply in_eq.
      unfold P_BF. intros. inversion H. subst. simpl. intuition. congruence. inversion H0.
      unfold P_ND2'. intros. inversion H0. inversion H1. subst.
      inversion H. inversion H2. subst. inversion H2. inversion H1.
      unfold P_Dup_Normal. intros. subst. inversion H0. inversion H1. subst.
      inversion H. inversion H2. inversion H2. inversion H1.
      unfold P_BF. intros. inversion H. subst. intros Hcontra.
      simpl in Hcontra.
      inversion Hcontra.
      congruence.
      inversion H0.
      congruence.
      exact H1.
      inversion H0.
      unfold P_BF. intros. inversion H.
    - apply ND_Lam.
      constructor. apply in_eq.
      unfold P_BF. intros. inversion H.
    - unfold P_ND2'. intros.
      inversion H0.
      2: inversion H1.
      inversion H1; subst.
      
      inversion H. inversion H2. inversion H2.
      inversion H3. inversion H3. inversion H4. inversion H4.
    - unfold P_Dup_Normal.
      intros.
      subst. inversion H0. inversion H1. subst. constructor. constructor. inversion H1.
    - unfold P_BF.
      intros.
      inversion H.
Qed.

(* PROBLEM: open terms
    (λ x λ y. x y ) (v y) would cause capture.

    Maybe fixed by adding Γ
*)

Definition t3_bad := Ty_App
        (Ty_Lam "X" KB (Ty_Lam "Y" KB (Ty_App (Ty_Var "X") (Ty_Var "Y"))))
        (Ty_App (Ty_Var "v") (Ty_Var "Y")).

Lemma t3_bad__not_wk :
    forall Δ Γ,
        (Δ : Γ ⊢ t3_bad) -> False.
Proof.
    intros.
    unfold t3_bad in H.
    inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    inversion H6; subst; clear H6.

    (*But Y must be in Γ*)
    inversion H3; subst; clear H3.
    inversion H2; subst; clear H2.

    contradiction H8 with (X := "Y").
    all: auto with *.
    simpl.
    right.
    left.
    reflexivity.
Qed.

(* This term steps to t3_bad *)
Definition t4_bad := Ty_App
    (Ty_Lam "W" KB ( Ty_App
        (Ty_Lam "X" KB (Ty_Lam "Y" KB (Ty_App (Ty_Var "X") (Ty_Var "Y"))))
        (Ty_Var "W")
    ))
    (Ty_App (Ty_Var "v") (Ty_Var "Y")).

Lemma t4_bad__not_wk :
    forall Δ Γ,
        (Δ : Γ ⊢ t4_bad) -> False.
Proof.
    intros.
    unfold t4_bad in H.
    inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    inversion H6; subst; clear H6.
    inversion H1; subst; clear H1.
    inversion H11; subst; clear H11.

    (*But Y must be in Γ*)
    inversion H3; subst; clear H3.
    inversion H6; subst; clear H6.

    contradiction H13 with (X := "Y").
    simpl.
    right. auto.
    simpl.
    right. left.
    reflexivity.
Qed.


(** Kinding of types *)
Reserved Notation "Δ '|-*' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_kind : list (string * kind) -> ty -> kind -> Prop :=
  | K_Var : forall Δ X K,
      lookup X Δ = Some K ->
      Δ |-* (Ty_Var X) : K
  | K_Lam : forall Δ X K1 T K2,
      ((X, K1) :: Δ) |-* T : K2 ->
      Δ |-* (Ty_Lam X K1 T) : (Kind_Arrow K1 K2)
  | K_App : forall Δ T1 T2 K1 K2,
      Δ |-* T1 : (Kind_Arrow K1 K2) ->
      (drop_btv Δ (btv T1)) |-* T2 : K1 -> (* This rule makes that a well-kinded type can never have capture when evaluated one step*)
      Δ |-* (Ty_App T1 T2) : K2
where "Δ '|-*' T ':' K" := (has_kind Δ T K).

Theorem well_kinded__no_capture :
    (* Maybe:
        Then if T is well_kinded with above has_kind,
        then it is also well_kinded with canonical has_kind
        And that then they normalise to same type?

        Probably, but seems like a lot of work.
    *) True
.


  (* Usual step relation that has no normality restrictions, 
    but with naive subsitutions.
*)
Inductive step : ty -> ty -> Set :=
    | step_beta (X : string) (K : kind) (S T : ty) :
        normal_Ty T ->
        step (Ty_App (Ty_Lam X K S) T) (substituteT X T S) 
    | step_appL S1 S2 T :
        neutral_Ty S1 ->
        step S1 S2 -> step (Ty_App S1 T) (Ty_App S2 T)
    | step_appR S T1 T2 :
        step T1 T2 -> step (Ty_App S T1) (Ty_App S T2)
    | step_abs bX K T1 T2 :
        step T1 T2 -> step (Ty_Lam bX K T1) (Ty_Lam bX K T2)
    .

Fixpoint count (X : string) (T: ty) : nat :=
    match T with
    | Ty_Var Y =>
        if X =? Y then 1 else 0
    | Ty_Lam Y K T' => 0 (* Not important *)
    | Ty_App T1 T2 =>
        count X T1 + count X T2
    end.

Fixpoint duplicate {A : Type} (l : list A) (n : nat ) := 
  match n with
  | O => nil
  | S n' => (l ++ (duplicate l n'))%list
  end.

(* collect binders*)
Fixpoint dsubst' (T : ty) : list (string * ty) :=
  match T with
  | Ty_Var X => []
  | Ty_Lam Y K T_body =>
    (Y, T_body)::(dsubst' T_body)
  | Ty_App T1 T2 =>
    dsubst' T1 ++ dsubst' T2
  end.

(* This is the property that we want to prove: that the step relation preserves the typing property *)

Fixpoint dsubst (Δ2 : list (string * ty)) (X : string) (U : ty) (T : ty): list (string * ty) :=
  match T with
  | Ty_Var Y => if X =? Y then Δ2 else nil
  | Ty_App T1 T2 => 
      (dsubst Δ2 X U T1 ++ dsubst Δ2 X U T2)%list
  | Ty_Lam Y K T_body =>
    if X =? Y then
      (Y, T_body)::(dsubst' T_body)
    else 
      (Y, substituteT X U T_body)::(dsubst Δ2 X U T_body)
  end.

Lemma BF_propertyΔ :
    forall (Δ : list (string * ty)) (Γ : list string) (T : ty) (X : string),
        Δ : Γ ⊢ T ->
        In X Γ -> ~ In X (map fst Δ).
Proof.
  intros Δ Γ T X Hnd.
  generalize dependent X.
  induction Hnd; intros.
  - auto.
  - destr_eqb_eq X X0.
    + unfold P_BF in H.
      apply H. auto.
    + simpl. intuition.
      specialize (IHHnd X0).
      apply IHHnd.
      apply in_cons.
      auto. auto.
  - rewrite map_app.
    apply not_in_app. split; eauto.
Qed.

(* This is the property that we want to prove: that the step relation preserves the typing property *)

(* HMM, I do not seem to use this for open U? *)
Theorem substituteT_preserves_NoDup : forall T Δ1 Δ2 Γ X U,
  P_ND2' ((X, T)::Δ1) Δ2 ->
  P_Dup_Normal ((X, T)::Δ1) Δ2 ->
  (* P_BF (((X, T)::Δ1) ++ Δ2) Γ -> *)  (* Hopefully we do not need this *)
  normal_Ty U ->
  Δ1 : (X :: Γ) ⊢ T ->
  Δ2 : Γ ⊢ U -> (* This lemma is used where X was in a lambda binder: hence, by the new typing rule, it may not occur free in U*)
  dsubst Δ2 X U T : Γ ⊢ (substituteT X U T).
Proof with eauto.
    
    intros T Δ1 Δ2 Γ X U HPND2 HDupNo HNo HndT HndU.
    generalize dependent Δ2.
    generalize dependent Δ1.
    generalize dependent Γ.
    generalize dependent U.
    
    induction T.
    - (* Var *)
      intros.
      simpl.
      destr_eqb_eq X s.
      + inversion HndT; subst.
        unfold dsubst. auto.
      + inversion HndT; subst.
        constructor.
        inversion HndT.
        subst.
        inversion H3; subst.
        congruence.
        auto.
    - (* Lam *)
      intros.
      
      simpl.
      destr_eqb_eq X s.
      + (* X = s*)
        exfalso.
        inversion HndT; subst.
        unfold P_BF in H5.
        specialize (H5 s).
        contradiction H5.
        apply in_eq. simpl. left. reflexivity.
      + (* X <> s *)
        inversion HndT; subst.
        
        assert (WK_Dup' Δ (X :: s :: Γ) T).
        {
            (* ADMIT: Weakening: cons_permute *)
            admit.
        }
        apply ND_Lam.
        eapply IHT; eauto.
        * (* ADMIT:
        TODO: This is the trickest case.
          U normal.   U can be of the form .... (λ(s: K). T) ...
          Then it must have kind >= kind of (λ (s : K). T), since this must be inside of
          a lambda body. it cannot be in head position by normality.
        
             What if X in Δ2? If it appears in there, it must have the exact same form:
            (X, Ty_Lam s k T), but that cannot be well-kinded... the argument must have smaller kind

            We cannot hide it in a const function or something: it is normal.
          *)
          admit.
        * (* ADMIT: By above, X cannot occur in Δ2, hence this hold trivially by above*)
           admit.
        * (* ADMIT: Weakening Gamma *) admit.
        * (* hmm, new case.
        
            
          *)
          unfold P_BF.
          intros.
          simpl.
          intuition.
          -- subst.
             unfold P_BF in H6.
             specialize (H6 X0).
             contradiction H6.
             apply in_cons. auto. simpl. left. reflexivity.
          -- (* By P_BF we know X0 not in the binders of T (i.e. Δ)
              What about Δ2?
              Can only happen if X free in T.
              
              So we would need: P_BF Δ2 Γ
            *)
            apply BF_propertyΔ with (X := X0) in HndU.
            (* Then we know X0 notin map fst Δ2!*)
            admit.
            auto.
    - intros.
      simpl.
      inversion HndT; subst.
      assert (dsubst Δ2 X U (Ty_App T1 T2) = (dsubst Δ2 X U T1 ++ dsubst Δ2 X U T2)%list).
      {
        simpl. reflexivity.
      }
      constructor; eauto.
      + eapply IHT1; eauto.
        * (* ADMIT:
            By P_ND2', if X in Δ2, then it is in there with (X, Ty_App T1 T2).
               That cannot be, that must be ill-kinded, since it is normal?

            Tricky tricky tricky (see also lam case):
            App case. Kind of U is smaller than kind of T1. So then how can the whole of 
              Ty_App T1 T2 be in U? It must then be normal (T1 neutral). Hence in whatever
              term, by normality, its kind will occur in the final kind: it cannot be 
              removed with some smart function or something, this is vague.

          *)
           admit.
        * (* See above, X cannot be in there.*)
          admit.
      + eapply IHT2; eauto.
        * (* ADMIT: see above *) admit.
        * (* ADMIT: see above *) admit.
      + (* Everything in Δ2 must for sure be normal, it will be in both sides.
            I think that it is by normality of U.
          Suppose (X, T) is a type in Δ0.

          If also (X, T') in Δ3, then T = T'.
          Then we substitute in identical terms, should be no problem.

          If X not in Δ3, but X in Δ2? By:
            P_Dup_Normal Δ0 Δ2
            and P_Dup_Normal Δ3 Δ2
          *)
      
      
        (* Unsure*) admit.
      + (* See above *)

        (* Unsure *) admit.
      + (*
          P_BF will decompose over app.
          Then dsubst will never have more binders than Δ0, Δ2, Δ3, U, added,
          and they all have no binders that are free in Γ by assumption.
            (Suppose U has a binder, then that binder is also in Δ2.)
        *)
      
        (* Unsure *) admit.

Admitted.

(* This is the property that we want to prove: that the step relation preserves the typing property *)
Theorem preservation' T1 T2 Δ Γ :
    Δ : Γ ⊢ T1 -> step T1 T2 -> exists Δ', Δ' : Γ ⊢ T2.
Proof.
    intros Hnd Hstep.
    generalize dependent Δ.
    generalize dependent Γ.
    induction Hstep; intros.
    - inversion Hnd; subst; clear Hnd.
      inversion H1; subst; clear H1.

      (* What do we know:
        T is WF under Δ2.
        T normal.
        Δ : (X :: Γ) ⊢ S,  so X free in S.
        We know, if X in Δ2, then S is normal.
        So why would this hold?
        Ftvs are not changed by substituteT, so let's ignore Gamma?

        From
          Δ : (X :: Γ) ⊢ S

          we should conclude

          f(Δ) : Γ ⊢ substituteT X T S

        I think maybe we know that (X, S)::Δ contains no duplicates.
          I think that follows from Δ : (X :: Γ) ⊢ S, the BF property.
        
        Let's say S = λY. (λZ. Y X) (λV. X)
        Then Δ = (Y, (λZ. Y X) (λV. X)) :: (Z, Y X) :: (V, X) :: nil)).
        
        This term would become (substituteT X T S) = (λY. (λZ. Y T) (λV. T)),
        but T the binders of T (say T = λW. W) should be carefully included into Δ.

        If T = λW. W, then substituteT X T S =
          (λY. (λZ. Y (λW. W)) (λV. (λW. W)))
        Which must have
          (Y, (λZ. Y (λW. W)) (λV. (λW. W))) :: (Z, Y (λ W. W))
            :: (W, W)
            :: (V, (λ W. W))
            :: (W, W)
           :: nil)).
          
        Maybe we can find some algorithm for that?
        We traverse Δ, whenever we see X, replace with T.
        Whenever in this entry X is not surrounded by a lambda anymore,
        add new entries Δ2

        So it is a function f(Δ, Δ2, X, T) that returns Δ'.

        But why would we have the properties?


      *)
      assert (dsubst Δ2 X T S : Γ ⊢ (substituteT X T S)).
      {
        eapply substituteT_preserves_NoDup; eauto.
      }
      exists (dsubst Δ2 X T S)%list.
      assumption.
      
    - (* Analogous to below *)
      admit.
    - inversion Hnd; subst.
      specialize (IHHstep Γ Δ2 H2) as [Δ2' Hnd2'].
      exists (Δ1 ++ Δ2')%list.
      constructor; auto.
      + (* Something, say (X, T) in Δ2' stepped. so we could have lost this property if 
            X is a key in Δ1. 
            But by P_Dup_Normal, we know that then it could not have stepped (by normality).
        *)
        admit.
      + (* P_DUP ? *)
        admit.
      + (* Δ2' is obtained from Δ2 by stepping. Hence bvs Δ2' are subset of bvs Δ2, so no problem*)
        admit.
    - inversion Hnd; subst.
      specialize (IHHstep (bX :: Γ) Δ0 H2) as [Δ0' Hnd0'].
      exists ((bX, T2)::Δ0')%list.
      constructor; auto.
Admitted.

(* Even after stepping, the type is still typeable in the more restrictive TyApp rule
  meaning that even after stepping, when stepping again, we will again not have capture
  i.e. this is the property that GU implies that is preserved
  under normalisation/betaReduction.
*)
Theorem preservation T1 T2 Δ K :
    Δ |-* T1 : K -> step T1 T2 -> Δ |-* T2 : K.
Proof.
    intros Hwk Hstep.
    generalize dependent Δ.
    generalize dependent K.
    induction Hstep; intros.
    - inversion Hwk; subst.
      inversion H2; subst.
      assert ((drop_btv Δ (btv S)) |-* T : K1).
      {
        (* Weakening, we coulud potentially add X, but it cannot be free in T by H4*)
        admit.
      }
      eapply substituteT_preserves_kinding; eauto.
    - inversion Hwk; subst.
      apply K_App with (K1 := K1).
      + eapply IHHstep; eauto.
      + (* stepping does not introduce new btvs, 
        but it could remove them, hence
            btv S2  subset of  btv S1

            Hence 
               inclusion (drop_btv Δ (btv s1)) (drop_btv Δ (btv s2))
            reasoning: btv s1 is bigger than btv s2: we remove more, hence lookup in the first implies still lookup in the second, which has every element in the first, and possibly more

            But what about shadowing??? I fear the existence of an X that becomes visible, but then that X was not necessary to begin with. So no issue.

        *)
        admit.
    - inversion Hwk; subst.
      apply K_App with (K1 := K1).
      + assumption.
      + eapply IHHstep; eauto.
    - inversion Hwk; subst.
      constructor.
      eapply IHHstep; eauto.
      
Admitted.
