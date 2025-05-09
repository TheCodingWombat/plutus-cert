From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

From PlutusCert Require Import Util.List.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
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

(* Usual step relation that has no normality restrictions, 
    but with naive subsitutions.
*)
Inductive step : ty -> ty -> Set :=
    | step_beta (X : string) (K : kind) (S T : ty) :
        step (Ty_App (Ty_Lam X K S) T) (substituteT X T S) 
    | step_appL S1 S2 T :
        step S1 S2 -> step (Ty_App S1 T) (Ty_App S2 T)
    | step_appR S T1 T2 :
        step T1 T2 -> step (Ty_App S T1) (Ty_App S T2)
    | step_abs bX K T1 T2 :
        step T1 T2 -> step (Ty_Lam bX K T1) (Ty_Lam bX K T2)
    .

Definition t1 := Ty_App (Ty_Lam "x" (Kind_Arrow Kind_Base Kind_Base) (Ty_Lam "y" Kind_Base (Ty_App (Ty_Var "x") (Ty_Var "y")))) (Ty_Lam "y" Kind_Base (Ty_Var "y")).

Definition t2 := (Ty_Lam "y" Kind_Base (Ty_App (Ty_Lam "y" Kind_Base (Ty_Var "y")) (Ty_Var "y"))).

Lemma t1_wk  : [] |-* t1 : (Kind_Arrow Kind_Base Kind_Base).
Proof.
  unfold t1.
  repeat econstructor.
Qed.

Lemma t1_steps_t2 : step t1 t2.
Proof.
  unfold t1, t2.
  repeat constructor.
Qed.

Lemma t2_wk : [] |-* t2 : (Kind_Arrow Kind_Base Kind_Base) -> False.
Proof.
  unfold t2.
  intros.
  inversion H; subst.
  inversion H2; subst.
  simpl in H6.
  inversion H6; subst.
  inversion H3; subst.
Qed.

  

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
