From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import micromega.Lia.

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

Fixpoint kind_size (k : kind) : nat :=
  match k with
  | Kind_Base => 1
  | Kind_Arrow K1 K2 => (kind_size K1) + (kind_size K2)
  end.

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

Definition P_ND2' (Δ1 Δ2 : list (string * (kind * ty))) :=
    forall X KT KT', In (X, KT) Δ1 -> In (X, KT') Δ2 -> KT = KT'.

(* If a binder occurs multiple times, and we started with a GU term,
    we must have had a beta reduction. This we only do with normal types.
*)
Definition P_Dup_Normal (Δ1 Δ2 : list (string * (kind * ty))) :=
    forall X T T' K1 K2, In (X, (K1, T)) Δ1 -> In (X, (K2, T')) Δ2 -> (K1, T) = (K2, T') -> normal_Ty T.

Definition P_BF (Δ : list (string * (kind *ty))) (Γ : list string) :=
    forall X, In X Γ -> ~ In X (map fst Δ).


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

(*
    Δ keeps track of lambda bodies, to make sure we never have dissimilar bodies for the same binder
    Γ keeps track of ftvs: no ftv may be bound somewhere else
*)
Reserved Notation "Ξ ,, Δ : Γ '⊢' T # K" (at level 40, Δ at level 0, Γ at level 0, T at level 0, no associativity).
Inductive WK : list (string * kind) -> list (string * (kind * ty)) -> list string -> ty -> kind -> Prop :=
  | ND_Var : forall Γ X Ξ K,
      In X Γ ->
      lookup X Ξ = Some K ->
      Ξ ,, [] : Γ ⊢ (Ty_Var X) # K   (* I changed this to nil, so that we cannot have random stuff in there*)
  | ND_Lam : forall Δ Γ X K1 T Ξ K2,
      ((X, K1)::Ξ) ,, Δ : (X::Γ) ⊢ T # K2 ->
      P_BF ((X, (K1, T))::Δ) Γ -> 

      Ξ ,, ((X, (K1, T))::Δ) : Γ ⊢ (Ty_Lam X K1 T) # (Kind_Arrow K1 K2)
  | ND_App : forall Δ1 Δ2 Γ T1 T2 Ξ K1 K2,
      Ξ ,, Δ1 : Γ ⊢ T1 # (Kind_Arrow K1 K2) ->
      Ξ ,, Δ2 : Γ ⊢ T2 # K1 ->
      P_ND2' Δ1 Δ2 ->
      P_Dup_Normal Δ1 Δ2 ->
      P_BF (Δ1 ++ Δ2) Γ ->
      Ξ ,, (Δ1 ++ Δ2) : Γ ⊢ (Ty_App T1 T2) # K2
where "Ξ ,, Δ : Γ '⊢' T # K" := (WK Ξ Δ Γ T K).


Create HintDb noDup_db.
Hint Constructors WK : noDup_db.

Definition KB := Kind_Base.

Lemma P_ND2'_sym Δ1 Δ2 :
  P_ND2' Δ1 Δ2 ->
  P_ND2' Δ2 Δ1.
Admitted.

(* 
(λX. λY. X Y)   (ΛY. Y)
*)
Definition t1_bad := Ty_App
        ( Ty_Lam "X" (Kind_Arrow KB KB) (Ty_Lam "Y" KB (Ty_App (Ty_Var "X") (Ty_Var "Y"))))
        (Ty_Lam "Y" KB (Ty_Var "Y")).

Lemma t1_bad__not_wk :
    forall Ξ Δ Γ K,
        (Ξ ,, Δ : Γ ⊢ t1_bad # K ) -> False.
Proof.
    intros.
    unfold t1_bad in H.
    inversion H; subst; clear H.
    inversion H3; subst; clear H3.
    inversion H2; subst; clear H2.
    inversion H6; subst; clear H6.
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
    forall Ξ Δ Γ K,
        (Ξ ,, Δ : Γ ⊢ t2_bad # K) -> False.
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
        (Ty_Lam "X" ((Kind_Arrow KB KB))
          (Ty_App (Ty_Lam "Y" (Kind_Arrow (Kind_Arrow KB KB) (Kind_Arrow KB KB)) (Ty_App (Ty_Var "Y") (Ty_Var "X"))) 
                  (Ty_Lam "Z" (Kind_Arrow KB KB) (Ty_Var "X"))))
        (Ty_Lam "V" KB (Ty_Var "V")).

Lemma t2_good__wk :
    exists Δ,
        ( nil ,, Δ : nil ⊢ t2_good # (Kind_Arrow KB KB)).
Proof with eauto with noDup_db.
    exists (
            (
             ("X", (Ty_App (Ty_Lam "Y" (Kind_Arrow (Kind_Arrow KB KB) (Kind_Arrow KB KB)) (Ty_App (Ty_Var "Y") (Ty_Var "X"))) (Ty_Lam "Z" (Kind_Arrow KB KB) (Ty_Var "X"))))
            ::([("Y", (Ty_App (Ty_Var "Y") (Ty_Var "X")))]
            ++ ("Z", (Ty_Var "X"))::nil))
            ++
            [("V", (Ty_Var "V"))])%list.
    unfold t2_good.
    apply ND_App with (K1 := (Kind_Arrow KB KB)).
    - apply ND_Lam.
      
      eapply ND_App.
      apply ND_Lam.
      assert ([("Y",
      Kind_Arrow (Kind_Arrow KB KB)
        (Kind_Arrow KB KB));
      ("X", Kind_Arrow KB KB)],,
      ([] ++ []) : ["Y"; "X"]
      ⊢ (Ty_App (Ty_Var "Y")
        (Ty_Var "X"))
      # Kind_Arrow KB KB).
      {
        econstructor.
        econstructor. apply in_eq. constructor. 
        + simpl. constructor. apply in_cons. apply in_eq. simpl.
          auto.
        + 
        
        unfold P_ND2'. intros. inversion H.
        +
          unfold P_Dup_Normal. intros. inversion H.
        + unfold P_BF. intros. intros Hcontra. simpl in Hcontra. assumption.
      }
      { rewrite <- empty_concat in H. assumption. }
      { unfold P_BF. intros. inversion H. subst. simpl. intuition. congruence. inversion H0. }
      { apply ND_Lam.
        constructor. apply in_cons. apply in_eq. simpl. auto.
        unfold P_BF. intros. inversion H. subst. simpl. intuition. congruence. inversion H0. }
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
      simpl. auto. 
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

Definition x0_double := Ty_Lam "X" KB (Ty_Lam "X" KB (Ty_Var "X")).

Lemma x0_double_wk :
        ([] ,, [("X", (KB, (Ty_Lam "X" KB (Ty_Var "X"))));("X", (KB, (Ty_Var "X")))] : [] ⊢ x0_double # (Kind_Arrow KB (Kind_Arrow KB KB))).
Proof.
  constructor.
  repeat constructor.
  unfold P_BF. intros. inversion H. subst. simpl. intuition.
  (* NO, not ok, which is good! *)
Admitted.

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
Fixpoint dsubst' (T : ty) : list (string * (kind * ty)) :=
  match T with
  | Ty_Var X => []
  | Ty_Lam Y K T_body =>
    (Y, (K, T_body))::(dsubst' T_body)
  | Ty_App T1 T2 =>
    dsubst' T1 ++ dsubst' T2
  end.

(* This is the property that we want to prove: that the step relation preserves the typing property *)

Fixpoint dsubst (Δ2 : list (string * (kind * ty))) (X : string) (U : ty) (T : ty): list (string * (kind * ty)) :=
  match T with
  | Ty_Var Y => if X =? Y then Δ2 else nil
  | Ty_App T1 T2 => 
      (dsubst Δ2 X U T1 ++ dsubst Δ2 X U T2)%list
  | Ty_Lam Y K T_body =>
    if X =? Y then
      (Y, (K, T_body))::(dsubst' T_body)
    else 
      (Y, (K, substituteT X U T_body))::(dsubst Δ2 X U T_body)
  end.

Lemma BF_propertyΔ :
    forall Ξ (Δ : list (string * (kind * ty))) (Γ : list string) (T : ty) K (X : string),
        Ξ ,, Δ : Γ ⊢ T # K ->
        In X Γ -> ~ In X (map fst Δ).
Proof.
  intros Ξ Δ Γ T K X Hnd.
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

Inductive SubTy : ty -> ty -> Prop :=
  | ST_Var : forall X,
      SubTy (Ty_Var X) (Ty_Var X)
  | ST_Lam : forall X K T1 T2,
      SubTy T1 T2 ->
      SubTy (Ty_Lam X K T1) (Ty_Lam X K T2)
  | ST_Lam2 : forall X Y K K2 T1 T2,
      SubTy (Ty_Lam X K T1) T2 ->
      SubTy (Ty_Lam X K T1) (Ty_Lam Y K2 T2)
  | ST_App : forall T1 T1' T2 T2',
      SubTy T2 T2' ->
      SubTy T1 T1' ->
      SubTy (Ty_App T1 T2) (Ty_App T1' T2')
  | ST_AppL : forall T1 T1' T2,
      SubTy T1 T1' ->
      SubTy T1 (Ty_App T1' T2)
  | ST_AppR : forall T1 T2 T2',
      SubTy T2 T2' ->
      SubTy T2 (Ty_App T1 T2').


Lemma subTy_refl T :
  SubTy T T.
Proof.
  induction T; simpl; constructor; auto.
Qed.

(* IF T1 is a subtype of T2, then it cannot have bigger kind
  WRONG IT CAN:
  Take T1 = x, with X in context * -> *
  Then T = x T2 for T2 : *, will have kind *.
*)
Lemma subTy_of_normal__smaller_kind Ξ Δ1 Δ2 Γ1 Γ2 T1 T2 K1 K2:
    Ξ ,, Δ1 : Γ1 ⊢ T1 # K1 ->
    Ξ ,, Δ2 : Γ2 ⊢ T2 # K2 ->
    SubTy T1 T2 -> normal_Ty T2 -> kind_size K1 <= kind_size K2.
Proof.
  intros Hwk1 Hwk2 Hsub Hnorm.
  generalize dependent Ξ.
  generalize dependent Δ1.
  generalize dependent Δ2.
  generalize dependent Γ1.
  generalize dependent Γ2.
  generalize dependent K1.
  generalize dependent K2.
  induction Hsub; intros.
  - inversion Hwk1; subst.
    inversion Hwk2; subst.
    assert (K1 = K2).
    {
      rewrite H6 in H4.
      inversion H4.
      auto.
    }
    subst.
    lia.
  - inversion Hwk1; subst.
    inversion Hwk2; subst.
    simpl.
    assert (kind_size K3 <= kind_size K0).
    {
      eapply IHHsub; eauto.
      inversion Hnorm; subst; auto.
      inversion H.
    }
    lia.
  - inversion Hwk1; subst.
    inversion Hwk2; subst.
    admit.
  - (* T1' T2' is normal, then the whole thing is neutral
      what do we know about kind_size of neutral things? probably the sum
    *)
  
    inversion Hwk1; subst.
    inversion Hwk2; subst.
    assert (kind_size K0 <= kind_size K3).
    {
      eapply IHHsub1; eauto.
      inversion Hnorm; subst; auto.
      inversion H. subst.
      assumption.
    }
    assert (kind_size (Kind_Arrow K0 K1) <= kind_size (Kind_Arrow K3 K2)).
    {
      eapply IHHsub2; eauto.
      inversion Hnorm; subst; auto.
      inversion H0; subst.
      apply NO_neutral in H11. assumption.
    }
    simpl in H0.
    (* kind_size K1, is the kind_size of the application*)
    admit.
  - 
Admitted.

Lemma kind_size_not_zero K :
  kind_size K > 0.
Proof.
  induction K; simpl; auto.
  lia.
Qed.

Lemma btv_implies_Δ {Ξ Δ Γ T K X} :
  Ξ ,, Δ : Γ ⊢ T # K -> 
  In X (btv T) -> 
  In X (map fst Δ).
Proof.
Admitted.

Lemma Δ_implies_subTy Ξ Δ Γ T K X T' K' :
  Ξ ,, Δ : Γ ⊢ T # K -> 
  In (X, (K', T')) Δ -> 
  SubTy (Ty_Lam X K' T') T.
Proof.
  intros Hwk Hin.
  generalize dependent T'.
  generalize dependent K'.
  induction Hwk; subst; intros.
  - inversion Hin.
  - inversion Hin.
    + inversion H0; subst.
      apply subTy_refl.
    + specialize (IHHwk K' T' H0).
      apply ST_Lam2.
      assumption.
  - apply in_app_or in Hin.
    destruct Hin as [Hin1 | Hin2].
    + apply ST_AppL.
      eapply IHHwk1; eauto.
    + apply ST_AppR.
      eapply IHHwk2; eauto.
Qed.


Lemma wk_norm_P2 X T Δ Δ2 KU Ξ Γ K U :
  P_ND2' ((X, (KU, T))::Δ) Δ2 ->
  Ξ ,, ((X, (KU, T))::Δ) : Γ ⊢ Ty_Lam X KU T # Kind_Arrow KU K ->
  Ξ ,, Δ2 : Γ ⊢ U # KU ->
  normal_Ty U ->
  ~ In X (map fst Δ2).
Proof.
  assert (kind_size KU < kind_size (Kind_Arrow KU K)).
  {
    simpl.
    remember (kind_size KU) as n.
    assert (kind_size K > 0).
    {
      apply kind_size_not_zero.
    }
    lia.
  }
  intros.
  intros Hcontra.
  assert (kind_size (Kind_Arrow KU K) <= kind_size KU).
  {
    eapply subTy_of_normal__smaller_kind; eauto.
    assert (In (X, (KU, T)) Δ2).
    {
      
      unfold P_ND2' in H0.
      apply in_map_iff in Hcontra as [[X' [K' T']] [Hfst Hsnd]].
      inversion Hfst. simpl in H4. subst. simpl.
      assert ((KU, T) = (K', T')).
      {
        eapply H0; eauto.
        simpl.
        left. auto.
      }
      inversion H5.
      subst.
      assumption.
    }
    eapply Δ_implies_subTy; eauto.
  }
  lia.
Qed.

(* Some property about duplicates and normality*)
Lemma wk_norm_P X T Δ Δ2 KU Ξ Γ K U :
  ~ In X Γ ->
  P_ND2' ((X, (KU, T))::Δ) Δ2 ->
  ((X, KU)::Ξ) ,, Δ : (X :: Γ) ⊢ T # K ->
  Ξ ,, Δ2 : Γ ⊢ U # KU ->
  normal_Ty U ->
  ~ In X (map fst Δ2).
Proof.
  (* My intuitioin: Then λ X KU T is a SubTy of U, and that cannot be well-kinded,  *)
  intros.
  intros.
  eapply wk_norm_P2; eauto.
  constructor.
  eauto.
  unfold P_BF.
  intros.
  simpl.
  intuition.
  subst.
  intuition.
  eapply BF_propertyΔ in H1.
  eauto. apply in_cons. auto.
Qed.

Lemma P_ND2'_app Δ1 Δ1' Δ2 :
  P_ND2' (Δ1 ++ Δ1')%list Δ2 ->
  P_ND2' Δ1 Δ2 /\ P_ND2' Δ1' Δ2.
Proof.
  intros.
  split.
  + unfold P_ND2' in H.
    unfold P_ND2'.
    intros.
    eapply H.
    apply in_app_iff.
    left. auto. eauto. auto.
  + unfold P_ND2' in H.
    unfold P_ND2'.
    intros.
    eapply H.
    apply in_app_iff.
    right. auto. eauto. auto.
Qed.

Lemma P_ND2'_cons X K T Δ1 Δ2 :
  P_ND2' ((X, (K, T))::Δ1) Δ2 ->
  P_ND2' Δ1 Δ2.
Proof.
  intros.
  unfold P_ND2' in H.
  unfold P_ND2'.
  intros.
  eapply H.
  apply in_cons. eauto. auto.
Qed.

Lemma P_Dup_Normal_app Δ1 Δ1' Δ2 :
  P_Dup_Normal (Δ1 ++ Δ1')%list Δ2 ->
  P_Dup_Normal Δ1 Δ2 /\ P_Dup_Normal Δ1' Δ2.
Admitted.

Lemma P_Dup_Normal_cons X K T Δ1 Δ2 :
  P_Dup_Normal ((X, (K, T))::Δ1) Δ2 ->
  P_Dup_Normal Δ1 Δ2.
Admitted.

Lemma P_BF_App Δ1 Δ2 Γ :
  P_BF (Δ1 ++ Δ2) Γ <->
  P_BF Δ1 Γ /\ P_BF Δ2 Γ.
Admitted.

Lemma dsubst_split Δ2 X X0 U T :
  In X (map fst (dsubst Δ2 X0 U T)) -> (In X (map fst Δ2) \/ In X (btv T)).
Proof.
Admitted.

Lemma dsubst_split2 Δ2 X X0 U T T':
  In (X, T') ( (dsubst Δ2 X0 U T)) -> (In (X, T') (Δ2) \/ In (X, T') (dsubst' T)).
Proof.
Admitted.

(* In other words: λx. λx. y   is not allowed! because same binder name binds different bodies*)
Lemma P_ND2'_refl Ξ ΔU Γ U KU :
  Ξ ,, ΔU : Γ ⊢ U # KU ->
  P_ND2' ΔU ΔU.
Proof.
  intros Hwk.
  unfold P_ND2'.
  intros.
  generalize dependent KT.
  generalize dependent KT'.
  generalize dependent X.
  induction Hwk; intros.
  - inversion H1.
  - destr_eqb_eq X X0.
    + subst.
      apply BF_propertyΔ with (X := X0) in Hwk; eauto.
      * inversion H0.
        -- inversion H2; subst.
           inversion H1; subst.
            inversion H3; subst. auto.
            eapply in_map with (f := fst) in H3.
            simpl in H3.
            contradiction.
        -- inversion H0; inversion H1.
            inversion H3; subst. inversion H4; subst. auto.
            eapply in_map with (f := fst) in H2.
            contradiction.
            eapply in_map with (f := fst) in H3.
            contradiction.
            eapply in_map with (f := fst) in H4.
            contradiction.

      * apply in_eq.
    + inversion H0.
      * inversion H3. contradiction.
      * inversion H1. inversion H4. contradiction.
        eapply IHHwk; eauto.
  - apply in_app_or in H2 as [H2 | H2].
    + eapply IHHwk1; eauto.
      apply in_app_or in H3 as [H3 | H3].
      auto. 
      unfold P_ND2' in H.
      specialize (H X KT' KT H2 H3).
      subst.
      auto.
    + eapply IHHwk2; eauto.
      apply in_app_or in H3 as [H3 | H3].
      auto.
      unfold P_ND2' in H.
      specialize (H X KT KT' H3 H2).
      subst.
      auto. auto.
Qed.

Lemma P_Dup_Normal_refl Ξ ΔU Γ U KU :
  Ξ ,, ΔU : Γ ⊢ U # KU ->
  normal_Ty U ->
  P_Dup_Normal ΔU ΔU.
Proof.
  intros.
  unfold P_Dup_Normal.
  intros.
  inversion H3; subst; clear H3.
  generalize dependent T'.
  generalize dependent K2.
  generalize dependent X.
  induction H; intros.
  - inversion H2.
  - inversion H2; subst.
    + inversion H4; subst.
      inversion H0; subst.
      assumption.
      inversion H5.
    + eapply IHWK; eauto.
      inversion H0; subst; auto.
      inversion H5.
  - apply in_app_or in H5 as [H5 | H5].
    + eapply IHWK1; eauto.
      inversion H0; subst; auto.
      inversion H7; subst.
      apply NO_neutral in H10.
      assumption.
    + eapply IHWK2; eauto.
      inversion H0; subst; auto.
      inversion H7; subst.
      apply NO_neutral in H10.
      assumption.
Qed.

    

Lemma P_ND2'_dsubst Ξ KU Γ Δ1 Δ2 ΔU X U T1 T2 K1 K2:
  Ξ ,, ΔU : Γ ⊢ U # KU ->
  ((X, KU)::Ξ) ,, Δ1 : (X:: Γ) ⊢ T1 # K1 ->
  ((X, KU)::Ξ) ,, Δ2 : (X :: Γ ) ⊢ T2 # K2 ->
  P_ND2' Δ1 Δ2 ->
  P_ND2' ΔU Δ1 ->
  P_ND2' ΔU Δ2 ->
  P_Dup_Normal Δ1 Δ2 ->
  normal_Ty U ->
  (P_ND2' (dsubst ΔU X U T1) (dsubst ΔU X U T2) /\ 
    P_Dup_Normal (dsubst ΔU X U T1) (dsubst ΔU X U T2)).
Proof.
  intros Hwk_U Hwk_T1 Hwk_T2 HPND2'_T HPDN_T Hnorm_U.
  assert (HP_ND2'_ΔU: P_ND2' ΔU ΔU).
  {
    eapply P_ND2'_refl; eauto.
  }
  split.
  - unfold P_ND2'.
    intros X0 KT KT' HIn_dT1 HIn_dT2.
    (* Suppose (X0, KT) is in dsubst ΔU X U T1,
      Then it is originally a lambda in T1, or in ΔU,
        or it is a binder in substituteT X U T1

        What if T1 = λ (Y.Y).

        And T2 = X (λY.Y)

        Then dsubst ΔU X U T1 = [(Y, Y)]

        dsubst ΔU X U T2 = ΔU ++ [Y, Y].
        Now, this is only problematic if there is then some binder Y in ΔU, that maps to something else
          than Y. But that is not allowed by P_ND2' ΔU Δ2.

        Hmm. But do we have some sort of no_dup of binders?
    *)

    admit.
  - 
      
      
        (* Unsure*) admit.
Admitted.

(* When stepping, we never introduce new binders (no capture-avoiding stuff)*)
Lemma P_BF_step Δ1 Δ1' Ξ Γ T1 T1' K :
  P_BF Δ1 Γ ->
  Ξ ,, Δ1 : Γ ⊢ T1 # K ->
  Ξ ,, Δ1' : Γ ⊢ T1' # K ->
  step T1 T1' ->
  P_BF Δ1' Γ.
Admitted.

Lemma P_ND2'_step Δ1 Δ2 Δ2' Ξ Γ T2 T2' K2 K2' :
  P_ND2' Δ1 Δ2 ->
  P_Dup_Normal Δ1 Δ2 ->
  step T2 T2' ->
  Ξ ,, Δ2 : Γ ⊢ T2 # K2 ->
  Ξ ,, Δ2' : Γ ⊢ T2' # K2' ->
  (P_ND2' Δ1 Δ2' /\ P_Dup_Normal Δ1 Δ2').
Proof.
  intros PND_Δ2 PDupN_Δ2 Hstep Hwk_T2 Hwk_T2'.
  split.
  - unfold P_ND2'.
    intros X KT KT' HIn_Δ1 HIn_Δ2'.
    (* If X, KT in Δ2' and Δ1, then (X, KT) in Δ2*)
    (* If (X, KT') in Δ2' then there must be a key X in Δ2
    *)
    assert (In (X, KT) Δ2).
    {
      (* By P_ND2' Δ1 Δ2, then it must be (X, KT), and by P_Dup_Normal, KT is normal*)
      admit.
    }
    assert (normal_Ty (snd KT)) by admit.
    (* By P_ND2'_Dup, we know that all X-lambdas in Δ2 are normal and equal.
      Δ2 corresponds to T2, so all X-lambdas in T2 are normal and equal

      Step T2 T2'

      This step cannot have occured inside of one of these lambdas, because they are normal
      It could have beta reduced?

      T2 = (λV. (λX. f(V)))) (P!)

      Then only problematic if also (λX. V) in Δ1.
      But that is not possible, then v free in T1.
       What if it is bound in T1?
       Then it must be the same as in T2, and that is not possible, because not normal...

       hmmmmm subtle....
      Suppose (λX. f(V)) changed. then there must have been an variable in there.
      call it V.
      Then V must have been bound in T2, otherwise it would not have been substituted.
      
      We only have a problem if also (λX. f(V)) in Δ1.
      V can either be free or bound in T1.
      - V free in T1:
        Then V free in T1, and bound in T2. But by
          Ξ,, Δ : Γ ⊢ (Ty_App T1 T2) # K
        We have BF Δ Γ. And then V in fst Δ, and V in Γ. contradiction.
      - V bound in T1. i.e. (λV. ... f(V))
        Then because V also bound in T2, and P_ND2' Δ1 Δ2, we must have
           (V, (K, λX. f(V))) in Δ2. But fuck. That is fine.

      Hmm. But with real beta reduction with our step function, this situation can never happen
      We only start substituting (and hence doubling, once nothign can be substituted 
      in this term anymore (a λv surround it can not exist: it cannot have been in Δ1
      by BF).

    )
    *)



    admit.
Admitted.

(* This is the property that we want to prove: that the step relation preserves the typing property *)

(* HMM, I do not seem to use this for open U? *)
Theorem substituteT_preserves_NoDup : forall Ξ T Δ1 Δ2 Γ X U KU K,
  P_ND2' (Δ1) Δ2 ->
  P_Dup_Normal (Δ1) Δ2 ->
  normal_Ty U ->
  ((X, KU)::Ξ) ,, Δ1 : (X :: Γ) ⊢ T # K  ->
  Ξ ,, Δ2 : Γ ⊢ U # KU -> (* This lemma is used where X was in a lambda binder: hence, by the new typing rule, it may not occur free in U*)
  P_BF (((X, (KU, T))::nil)) Γ ->  (* Hopefully we do not need this *)
  Ξ ,, (dsubst Δ2 X U T) : Γ ⊢ (substituteT X U T) # K.
Proof with eauto.
    
    intros Ξ T Δ1 Δ2 Γ X U KU K HPND2 HDupNo HNo HndT HndU HBF.
    generalize dependent Δ2.
    generalize dependent Δ1.
    generalize dependent Γ.
    generalize dependent U.
    generalize dependent Ξ.
    generalize dependent K.
    generalize dependent KU.
    generalize dependent X.
    
    induction T; intros.
    - (* Var *)
      simpl.
      destr_eqb_eq X s.
      + inversion HndT; subst.
        unfold dsubst. auto.
        simpl in H4. rewrite String.eqb_refl in H4. inversion H4. subst. assumption.
      + inversion HndT; subst.
        constructor.
        * simpl in H1.
          destruct H1; auto.
          contradiction.
        * simpl in H5.
          rewrite <- String.eqb_neq in H.
          rewrite H in H5.
          assumption.
    - (* Lam *)
      intros.
      
      simpl.
      destr_eqb_eq X s.
      + (* X = s*)
        exfalso.
        inversion HndT; subst.
        unfold P_BF in H7.
        specialize (H7 s).
        contradiction H7.
        apply in_eq. simpl. left. reflexivity.
      + (* X <> s *)
        inversion HndT; subst.
        
        assert (WK ((X, KU)::(s, k)::Ξ) Δ (X :: s :: Γ) T K2).
        {
            (* ADMIT: Weakening: cons_permute *)
            admit.
        }
        apply ND_Lam.
        {
          eapply IHT; eauto.
          * unfold P_BF.
            intros.
            inversion H1.
            subst. simpl. intuition. simpl. intuition. 
            subst.
            unfold P_BF in HBF.
            simpl in HBF.
            specialize (HBF X0 H2).
            intuition.
          
          * eapply P_ND2'_cons; eauto.
          * eapply P_Dup_Normal_cons; eauto.
          * (* ADMIT: Weakening Gamma *) 
            (* 
              What if s is already in Ξ? 
              By P_BF we know s not free in Gamma.
              Then s not free in U.
              Then s not necessary in Ξ, then we might shadow, but it is not important.
              *)
            admit.
          
            
          
        }
        unfold P_BF.
        intros.
        simpl.
        intuition.
        -- subst.
          unfold P_BF in H8.
          specialize (H8 X0).
          contradiction H8.
          apply in_cons. auto. simpl. left. reflexivity.
        -- apply BF_propertyΔ with (X := X0) in HndU; eauto.
           assert (In X0 (map fst Δ2) \/ In X0 (btv T)).
           {
            eapply dsubst_split; eauto.
           }
           destruct H2 as [H2 | H2].
           ++ contradiction.
           ++ assert (In X0 (map fst Δ)).
              {
                eapply btv_implies_Δ; eauto.
              }
              unfold P_BF in H8.
              specialize (H8 X0).
              assert (In X0 (X :: Γ)).
              {
                simpl. intuition.
              }
              specialize (H8 H5).
              simpl in H8.
              intuition.
            

    - intros.
      simpl.
      inversion HndT; subst.
      
      econstructor; eauto.
      + eapply IHT1; eauto.
        * eapply P_ND2'_app in HPND2 as [HPND2 _].
          assumption.
        * eapply P_Dup_Normal_app in HDupNo as [HDupNo _].
          assumption.
      + eapply IHT2; eauto.
        * eapply P_ND2'_app in HPND2 as [_ HPND2].
          assumption.
        * eapply P_Dup_Normal_app in HDupNo as [_ HDupNo].
          assumption.
      + eapply P_ND2'_dsubst with (Ξ := Ξ) (Δ1 := Δ0) (Δ2 := Δ3); eauto.
        * eapply P_ND2'_app in HPND2 as [HPND2 _].
          apply P_ND2'_sym.
          assumption.
        * eapply P_ND2'_app in HPND2 as [_ HPND2].
          apply P_ND2'_sym.
          assumption.
      + eapply P_ND2'_dsubst with (Δ1 := Δ0) (Δ2 := Δ3); eauto.
        * eapply P_ND2'_app in HPND2 as [HPND2 _].
          apply P_ND2'_sym.
          assumption.
        * eapply P_ND2'_app in HPND2 as [_ HPND2].
          apply P_ND2'_sym.
          assumption.
      + apply P_BF_App.
        apply P_BF_App in H9 as [P_BFΔ0 P_BFΔ3].
        split.
        * unfold P_BF.
          intros.
          intros Hcontra.
          apply dsubst_split in Hcontra.
          destruct Hcontra as [Hcontra | Hcontra].
          -- eapply BF_propertyΔ in HndU; eauto.
          -- apply (btv_implies_Δ H1) in Hcontra.
             eapply BF_propertyΔ in H1; eauto.
             apply in_cons. assumption.
        * unfold P_BF.
          intros.
          intros Hcontra.
          apply dsubst_split in Hcontra.
          destruct Hcontra as [Hcontra | Hcontra].
          -- eapply BF_propertyΔ in HndU; eauto.
          -- apply (btv_implies_Δ H2) in Hcontra.
             eapply BF_propertyΔ in H2; eauto.
             apply in_cons. assumption.
Admitted.

(* This is the property that we want to prove: that the step relation preserves the typing property *)
Theorem preservation' Ξ T1 T2 Δ Γ K :
    Ξ ,, Δ : Γ ⊢ T1 # K -> step T1 T2 -> exists Δ', Ξ ,, Δ' : Γ ⊢ T2 # K.
Proof.
    intros Hnd Hstep.
    generalize dependent Δ.
    generalize dependent Γ.
    generalize dependent K.
    generalize dependent Ξ.
    induction Hstep; intros.
    - inversion Hnd; subst; clear Hnd.
      inversion H1; subst; clear H1.

      assert (Ξ ,, (dsubst Δ2 X T S) : Γ ⊢ (substituteT X T S) # K0).
      {
        eapply substituteT_preserves_NoDup with (Δ1 := Δ); eauto.
        + eapply P_ND2'_cons; eauto.
        + eapply P_Dup_Normal_cons; eauto.
        + unfold P_BF.
          intros. simpl.
          intuition.
          subst.
          unfold P_BF in H13.
          specialize (H13 X0 H).
          simpl in H13.
          intuition.
      }
      exists (dsubst Δ2 X T S)%list.
      assumption.
      
    - (* Analogous to below *)
      admit.
    - inversion Hnd; subst.
      specialize (IHHstep Ξ K1 Γ Δ2 H2) as [Δ2' Hnd2'].
      exists (Δ1 ++ Δ2')%list.
      apply ND_App with (K1 := K1); auto.
      + eapply P_ND2'_step with (Δ2 := Δ2) (K2' := K1) (K2 := K1); eauto.
      + eapply P_ND2'_step with (Δ2 := Δ2) (K2' := K1) (K2 := K1); eauto.
      + apply P_BF_App in H9 as [H9 H10].
        apply P_BF_App; split; auto.
        eapply P_BF_step; eauto.
    - inversion Hnd; subst.
      specialize (IHHstep ((bX, K)::Ξ) K2 (bX :: Γ) Δ0 H6) as [Δ0' Hnd0'].
      exists ((bX, (K, T2))::Δ0')%list.
      constructor; auto.
      inversion Hnd0'; subst.
      + unfold P_BF. intros. unfold P_BF in H7.
        specialize (H7 X0 H1).
        simpl.
        simpl in H7.
        intuition.
      + unfold P_BF. intros.
        simpl. intuition.
        -- subst.
            unfold P_BF in H7.
            specialize (H7 X0 H1).
            simpl in H7.
            intuition.
         -- subst.
            unfold P_BF in H0.
            specialize (H0 X0).
            assert (In X0 (bX :: Γ)).
            {
              simpl. intuition.
            }
            specialize (H0 H2).
            simpl in H0.
            intuition.
         -- unfold P_BF in H0.
            contradiction H0 with (X := X0).
            apply in_cons. assumption.
            simpl. right. auto.
      + unfold P_BF.
        intros.
        simpl.
        intuition; subst.
        eapply BF_propertyΔ in Hnd; eauto.
        simpl in Hnd. intuition.
        rewrite map_app in H8.
        apply in_app_or in H8 as [H8 | H8].
        * eapply BF_propertyΔ in H; eauto.
          apply in_cons. assumption.
        * eapply BF_propertyΔ in H0; eauto.
          apply in_cons. assumption.
Admitted.