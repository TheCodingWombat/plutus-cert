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

(* Even after stepping, the type is still typeable in the more restrictive TyApp rule*)
Theorem preservation T1 T2 Δ K :
    Δ |-* T1 : K -> step T1 T2 -> Δ |-* T2 : K.
Proof.
    intros Hwk Hstep.
    generalize dependent Δ.
    generalize dependent K.
    induction Hstep; intros.
    - inversion Hwk; subst.
      inversion H2; subst.
      (* By weakening Δ |-* T : K1 then by substituteT_preserves_kinding (should also hold for open U, see substituteTCA_preserves_kinding) *)
      admit.
    - inversion Hwk; subst.
      apply K_App with (K1 := K1).
      + eapply IHHstep; eauto.
      + (* stepping does not introduce new btvs, 
        but it could remove them, hence
            btv S2  subset of  btv S1

            Hence 
               inclusion (drop_btv Δ (btv s1)) (drop_btv Δ (btv s2))

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
