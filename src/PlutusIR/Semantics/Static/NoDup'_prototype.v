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

(* It may already be present, but only with the same body *)
Definition P_ND (X : string) (T : ty) (Δ : list (string * ty)) := 
  forall T', lookup X Δ = Some T' -> T = T'.

(* Not strong enough. Even when shadowed things have different T, it is a problem*)
Definition P_ND2 (Δ1 Δ2 : list (string * ty)) :=
    forall X T T', lookup X Δ1 = Some T -> lookup X Δ2 = Some T' -> T <> T' -> False.

Definition P_ND2' (Δ1 Δ2 : list (string * ty)) :=
    forall X T T', In (X, T) Δ1 -> In (X, T') Δ2 -> T <> T' -> False.

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
  | ND_Var : forall Δ Γ X,
      In X Γ ->
      Δ : Γ ⊢ (Ty_Var X) 
  | ND_Lam : forall Δ Γ X K1 T ,
      Δ : (X::Γ) ⊢ T ->
      
      (* P_ND X T Δ ->  *)
      (* Do we need this? *)
      ((X, T)::Δ) : Γ ⊢ (Ty_Lam X K1 T)
  | ND_App : forall Δ1 Δ2 Γ T1 T2 ,
      Δ1 : Γ ⊢ T1 ->
      Δ2 : Γ ⊢ T2 ->
      P_ND2' Δ1 Δ2 ->
      (* P_Dup_Normal Δ1 Δ2 -> *)
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
    inversion H3; subst; clear H3.
    contradiction H6 with (X := "Y") (T := Ty_App (Ty_Var "X") (Ty_Var "Y"))
                (T' := (Ty_Var "Y")); auto with *.
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
    inversion H4; subst; clear H4.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    inversion H3; subst; clear H3.
    inversion H2; subst; clear H2.

    contradiction H6 with (X := "Y") (T := (Ty_Var "Y")) (T' := (Ty_App (Ty_Var "X") (Ty_Var "Y"))).
    all: auto with *.
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
      unfold P_BF. intros. intros Hcontra. simpl in Hcontra. assumption.
      apply ND_Lam.
      constructor. apply in_cons. apply in_eq.
      unfold P_ND2'. intros. inversion H0. inversion H2. subst.
      inversion H. inversion H3. inversion H3.
      inversion H2.
      unfold P_BF. intros. inversion H. subst. intros Hcontra.
      simpl in Hcontra.
      inversion Hcontra.
      congruence.
      inversion H0.
      congruence.
      exact H1.
      inversion H0.
    - apply ND_Lam.
      constructor. apply in_eq.
    - unfold P_ND2'. intros.
      inversion H0.
      2: inversion H2.
      inversion H2; subst.
      
      inversion H. inversion H3. inversion H3.
      inversion H4. inversion H4. inversion H5. inversion H5.
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
    inversion H4; subst; clear H4.

    (*But Y must be in Γ*)
    inversion H3; subst; clear H3.
    inversion H4; subst; clear H4.

    contradiction H7 with (X := "Y").
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
    inversion H4; subst; clear H4.
    inversion H1; subst; clear H1.
    inversion H5; subst; clear H5.

    (*But Y must be in Γ*)
    inversion H3; subst; clear H3.
    inversion H5; subst; clear H5.

    contradiction H7 with (X := "Y").
    simpl.
    right. right. left.
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
        normal_Ty S ->
        normal_Ty T ->
        step (Ty_App (Ty_Lam X K S) T) (substituteT X T S) 
    | step_appL S1 S2 T :
        step S1 S2 -> step (Ty_App S1 T) (Ty_App S2 T)
    | step_appR S T1 T2 :
        normal_Ty S ->
        step T1 T2 -> step (Ty_App S T1) (Ty_App S T2)
    | step_abs bX K T1 T2 :
        step T1 T2 -> step (Ty_Lam bX K T1) (Ty_Lam bX K T2)
    .

(* HMM, I do not seem to use this for open U? *)
Theorem substituteT_preserves_kinding : forall T Delta X K U L,
  ((X, L) :: Delta) |-* T : K ->
  (drop_btv Delta (btv T)) |-* U : L -> (* This lemma is used where X was in a lambda binder: hence, by the new typing rule, it may not occur free in U*)
  Delta |-* (substituteT X U T) : K.
Proof with eauto.
  induction T.
  all: intros Delta X K U L Hkind__T HHkind__U.
  all: simpl.
  all: inversion Hkind__T; subst...
  - (* Ty_Var *)
    destruct (X =? s)%string eqn:Heqb.
    + (* X = Y *)
      apply eqb_eq in Heqb as Heq.
      subst.
      assert (K = L).
      {
        simpl in H1.
        rewrite Heqb in H1.
        inversion H1; auto.
      }
      subst.
      (* ADMIT: weakening *)
      admit.
    + (* X <> Y *)
      apply eqb_neq in Heqb as Hneq.
      rewrite lookup_neq in H1...
      constructor.
      assumption.
  - (* Ty_Lam *)
    rename s into bX.
    destruct (X =? bX)%string eqn:Heqb.
    + (* X = bX *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply K_Lam...
      (* ADMIT: Weakening shadow *)
      admit.
    + (* X <> bX *)
      apply eqb_neq in Heqb as Hneq.
      apply K_Lam.
      eapply IHT...
      * (* ADMIT: Weakening cons permute *)
        admit.
      * simpl.
        destruct (in_dec string_dec bX (btv T)); eauto.
        -- (* ADMIT: Weakening: now bX could be added to it, but it cannot shadow*)
           admit.
        -- (* U is well_kinded without bX, so we can add it without shadowing *)
           admit.
  - (* Ty_App *)
    apply K_App with (K1 := K1).
    + eapply IHT1...
      admit.
    + eapply IHT2...
      * (* If U contains btvs free in T2, then it all fails *)
        admit.
      * admit.
    
Admitted.




Fixpoint Δ_step (Δ : list (string * ty)) (T1 T2 : ty) : list (string * ty) :=
    match Δ with
    | nil => nil
    | (X, T)::Δ' =>
        if ty_eq T T1 then
            (X, T2)::(Δ_step Δ' T1 T2)
        else
            Δ_step Δ' T1 T2
    end.

Lemma Δ_step_app_rewrite : forall Δ1 Δ2 T1 T2,
    Δ_step (Δ1 ++ Δ2) T1 T2 = ((Δ_step Δ1 T1 T2) ++ (Δ_step Δ2 T1 T2))%list.
Admitted.

(* HMM, I do not seem to use this for open U? *)
Theorem substituteT_preserves_NoDup : forall T Δ1 Δ2 Γ X U,
  normal_Ty T ->
  normal_Ty U ->
  Δ1 : (X :: Γ) ⊢ T ->
  Δ2 : Γ ⊢ U -> (* This lemma is used where X was in a lambda binder: hence, by the new typing rule, it may not occur free in U*)
  Δ1 : Γ ⊢ (substituteT X U T).
Proof with eauto.
    intros T Δ1 Δ2 Γ X U HNo_T HNo_U HndT HndU.
    generalize dependent Δ2.
    generalize dependent Δ1.
    generalize dependent Γ.
    induction T.
    - intros.
      simpl.
      destr_eqb_eq X s.
      + admit.
      + eexists.
        constructor.
        inversion HndT.
        subst.
        inversion H3; subst.
        congruence.
        auto.
    - intros.
      simpl.
      destr_eqb_eq X s.
      + (* X = s*)
        inversion HndT; subst.
        eexists.
        constructor.
        (* Some weakening argument*)
        admit.
      + (* X <> s *)
        inversion HndT; subst.
        assert ((s, T) = (s, substituteT X U T)).
        {
            (* This is a problem *)
            admit.
        }
        assert (WK_Dup' Δ (X :: s :: Γ) T).
        {
            (* Some weakening argument*)
            admit.
        }
        inversion HNo_T; subst.
        specialize (IHT H4 _ _ H1).
        assert (WK_Dup' Δ2 (s :: Γ) U).
        {
            (* Some weakening argument*)
            admit.
        }
        specialize (IHT _ H2) as [Δ0 HndΔ0].
        exists ((s, substituteT X U T)::Δ0).
        apply ND_Lam.
        assumption.

        (* lam cannot be neutral *)
        inversion H2.
    - intros.
      simpl.
      inversion HndT; subst.
      inversion HNo_T; subst.
      inversion H; subst.
      apply NO_neutral in H5.
      specialize (IHT1 H5 _ _ H1 _ HndU) as [Δ1' IHT1].
      specialize (IHT2 H8 _ _ H2 _ HndU) as [Δ2' IHT2].
      exists (Δ1' ++ Δ2')%list.
      constructor; eauto.
      + admit.
      + admit.
      + admit.

Admitted.

(* This is the property that we want to prove: that the step relation preserves the typing property *)
Theorem preservation' T1 T2 Δ Γ :
    Δ : Γ ⊢ T1 -> step T1 T2 -> exists Δ', Δ' : Γ ⊢ T2.
Proof.
    intros Hnd Hstep.
    generalize dependent Δ.
    generalize dependent Γ.
    induction Hstep; intros.
    - inversion Hnd; subst.
      inversion H1; subst.
      eapply substituteT_preserves_NoDup; eauto.
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
      + (* Something in Δ2 could have stepped. But only if it didnt already occur in Δ1 by normality *)
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
