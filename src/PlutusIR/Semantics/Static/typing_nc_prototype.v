From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

From PlutusCert Require Import Util.List util.

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
  | Ty_Forall : string -> kind -> ty -> ty
  | Ty_Fun : ty -> ty -> ty
.

Fixpoint btv (T : ty) : (list string) :=
    match T with
    | Ty_Var x => []
    | Ty_Lam x K T0 => x :: (btv T0)
    | Ty_App T1 T2 => btv T1 ++ btv T2
    | Ty_Forall x K T0 => x :: (btv T0)
    | Ty_Fun T1 T2 => btv T1 ++ btv T2
    end.


  Function ftv (T : ty) : list string :=
    match T with
    | Ty_Var X =>
        [X]
    | Ty_Fun T1 T2 =>
        ftv T1 ++ ftv T2
    | Ty_Forall X K T' =>
        remove string_dec X (ftv T')
    | Ty_Lam X K1 T' =>
        remove string_dec X (ftv T')
    | Ty_App T1 T2 =>
        ftv T1 ++ ftv T2
    end.

Module Ty.
  Definition closed (T : ty) :=
    forall X, ~ In X (ftv T).
End Ty.

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
      Δ |-* T2 : K1 -> (* This rule makes that a well-kinded type can never have capture when evaluated one step*)
      Δ |-* (Ty_App T1 T2) : K2
  | K_Forall : forall Δ X K T,
      ((X, K) :: Δ) |-* T : Kind_Base ->
      Δ |-* (Ty_Forall X K T) : Kind_Base
  | K_Fun : forall Δ T1 T2,
      Δ |-* T1 : Kind_Base ->
      Δ |-* T2 : Kind_Base ->
      Δ |-* (Ty_Fun T1 T2) : Kind_Base
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
  | Ty_Forall Y K T' =>
    if X =? Y then Ty_Forall Y K T' else Ty_Forall Y K (substituteT X U T')
    | Ty_Fun T1 T2 =>
    Ty_Fun (substituteT X U T1) (substituteT X U T2)
  end.

(* HMM, I do not seem to use this for open U? *)
Theorem substituteT_preserves_kinding : forall T Delta X K U L,
  ((X, L) :: Delta) |-* T : K ->
  nil |-* U : L -> 
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
      (* ADMIT: weakening empty *)
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
      (* ADMIT: Weakening cons permute *)
      admit.
  - (* Ty_App *)
    econstructor; eauto.
  - (* Ty_Forall *)
    rename s into bX.
    destruct (X =? bX)%string eqn:Heqb.
    + (* X = bX *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply K_Forall...
      (* ADMIT: Weakening shadow *)
      admit.
    + (* X <> bX *)
      apply eqb_neq in Heqb as Hneq.
      apply K_Forall.
      eapply IHT...
      (* ADMIT: Weakening cons permute *)
      admit.
  - (* Ty_Fun *)
    econstructor; eauto.
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
    | step_funL S1 S2 T :
        step S1 S2 -> step (Ty_Fun S1 T) (Ty_Fun S2 T)
    | step_funR S T1 T2 :
        step T1 T2 -> step (Ty_Fun S T1) (Ty_Fun S T2)
    | step_forall K bX T1 T2 :
        step T1 T2 -> step (Ty_Forall bX K T1) (Ty_Forall bX K T2)
    .

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
      (* By weakening we have Δ |-* T : K1 then by substituteT_preserves_kinding (should also hold for open U, see substituteTCA_preserves_kinding) *)
      admit.
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
    - (* Analogous to appL *)
      admit.
    - (* Analogous to appR *)
      admit.
    - (* Analogous to abs *)
      admit.     
Admitted.

(* Mock normaliser without beta reduction*)
Fixpoint normaliser (T : ty) : option ty :=
  match T with
  | Ty_Var _ => Some T
  | Ty_Lam x K T' =>
    match normaliser T' with
    | Some Tn => Some (Ty_Lam x K Tn)
    | None => None
    end
  | Ty_App T1 T2 =>
    match normaliser T1, normaliser T2 with
    | Some T1n, Some T2n => Some (Ty_App T1n T2n)
    | _, _ => None
    end
  | Ty_Forall x K T' =>
    match normaliser T' with
    | Some Tn => Some (Ty_Forall x K Tn)
    | None => None
    end
  | Ty_Fun T1 T2 =>
    match normaliser T1, normaliser T2 with
    | Some T1n, Some T2n => Some (Ty_Fun T1n T2n)
    | _, _ => None
    end
  end.


(*******   Terms and their types   ******)
Inductive term :=
  | Var      : string -> term
  | TyAbs    : string -> kind -> term -> term
  | LamAbs   : string -> ty -> term -> term
  | Apply    : term -> term -> term
  | TyInst   : term -> ty -> term.


Fixpoint drop_ty_var' X (Γ : list (string * ty)) (acc : list string): list (string * ty) :=
  match Γ with
  | nil => nil
  | (x, T) :: Γ' =>
      if (in_dec string_dec X (ftv T)) then 
        drop_ty_var' X Γ' (x::acc)
      else if in_dec string_dec x acc then
        drop_ty_var' X Γ' acc
      else (x, T) :: drop_ty_var' X Γ' acc
  end.

Definition drop_ty_var X (Γ : list (string * ty)) : list (string * ty) :=
  drop_ty_var' X Γ nil.


Reserved Notation "Delta ',,' Gamma '|-+' t ':' T" (at level 101, t at level 0, T at level 0, no associativity).
Inductive has_type : list (string * kind) -> list (string * ty) -> term -> ty -> Prop :=
  (* Simply typed lambda caclulus *)
  | T_Var : forall Γ Δ x T Tn,
      lookup x Γ = Coq.Init.Datatypes.Some T ->
      Δ |-* T : Kind_Base ->
      normaliser T = Some Tn ->
      Δ ,, Γ |-+ (Var x) : Tn
  | T_LamAbs : forall Δ Γ x T1 t T2n T1n,
      Δ |-* T1 : Kind_Base ->
      normaliser T1 = Some T1n ->
      Δ ,, (x, T1n) :: Γ |-+ t : T2n ->
      Δ ,, Γ |-+ (LamAbs x T1 t) : (Ty_Fun T1n T2n)
  | T_Apply : forall Δ Γ t1 t2 T1n T2n,
      Δ ,, Γ |-+ t1 : (Ty_Fun T1n T2n) ->
      Δ ,, Γ |-+ t2 : T1n ->
      Δ ,, Γ |-+ (Apply t1 t2) : T2n
  (* Universal types *)
  | T_TyAbs : forall Δ Γ X K t Tn,
      ((X, K) :: Δ) ,, (drop_ty_var X Γ) |-+ t : Tn ->
      Δ ,, Γ |-+ (TyAbs X K t) : (Ty_Forall X K Tn)
  | T_TyInst : forall Δ Γ t1 T2 T1n X K2 T0n T2n,
      Δ ,, Γ |-+ t1 : (Ty_Forall X K2 T1n) ->
      (drop_btv Δ (btv T1n)) |-* T2 : K2 ->
      normaliser T2 = Some T2n ->
      normaliser (substituteT X T2n T1n) = Some T0n ->
      Δ ,, Γ |-+ (TyInst t1 T2) : T0n
where "Δ ',,' Γ '|-+' t ':' T" := (has_type Δ Γ t T).


Fixpoint subst (x : string) (s : term) (t : term) : term :=
  match t with
  | Var y =>
      if x =? y
        then s
        else Var y
  | TyAbs bX K t0 =>
      TyAbs bX K (subst x s t0)
  | LamAbs bx T t0 =>
      if x =? bx
        then LamAbs bx T t0
        else LamAbs bx T (subst x s t0)
  | Apply t1 t2 =>
      Apply (subst x s t1) (subst x s t2)
  | TyInst t0 T =>
      TyInst (subst x s t0) T
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20, x constr).


Fixpoint substA (X : string) (U : ty) (t : term) {struct t} : term :=
  match t with
  | Var y =>
      Var y
  | TyAbs bX K t0 =>
      if X =? bX
        then TyAbs bX K t0
        else TyAbs bX K (substA X U t0)
  | LamAbs bx T t0 =>
      LamAbs bx (substituteT X U T) (substA X U t0)
  | Apply t1 t2 =>
      Apply (substA X U t1) (substA X U t2)
  | TyInst t0 T =>
      TyInst (substA X U t0) (substituteT X U T)
  end.
Notation "':[' X ':=' U ']' t" := (substA X U t) (at level 20, X constr).


Reserved Notation "t '=[' j ']=>' v"(at level 40).
Inductive eval : term -> term -> nat -> Prop :=
  | E_LamAbs : forall j x T t,
      j = 0 ->
      LamAbs x T t =[j]=> LamAbs x T t
  | E_Apply : forall j t1 t2 x T t0 v2 v0 j1 j2 j0,
      j = j1 + j2 + 1 + j0 ->
      t1 =[j1]=> LamAbs x T t0 ->
      t2 =[j2]=> v2 ->
      ([x := v2 ] t0 ) =[j0]=> v0 ->
      Apply t1 t2 =[j]=> v0
  (** Universal types *)
  | E_TyAbs : forall j X K t,
      j = 0 ->
      TyAbs X K t =[j]=> TyAbs X K t
  | E_TyInst : forall j t1 T2 X K t0 v0 j1 j0,
      j = j1 + 1 + j0 ->
      t1 =[j1]=> TyAbs X K t0 ->
      (:[X := T2] t0) =[j0]=> v0 ->
      TyInst t1 T2 =[j]=> v0
where "t '=[' j ']=>' v" := (eval t v j).


(* TERM SUBSTITUTION PRESERVATION *)

Lemma substitution_preserves_typing :
  forall Delta Gamma x U Un v T t,
    Delta ,, ((x, U) :: Gamma) |-+ t : T ->
    normaliser U = Some Un ->
    nil ,, nil |-+ v : Un ->
    Delta ,, Gamma |-+ ([x := v] t) : T.
Proof with eauto.
    intros.
    generalize dependent Delta.
    generalize dependent Gamma.
    generalize dependent T.
    induction t; intros.
  all: intros; autounfold; intros.
  all: try solve [try (inversion H || inversion H0 || inversion H1); subst; eauto with typing].
  - (* Var *)
    simpl.
    destruct (x =? s)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      inversion H; subst.
      simpl in H3.
      rewrite Heqb in H3.
      inversion H3; subst; clear H3.
      assert (Un = T).
      { (*ADMIT: normalisation__deterministic *)admit. }
      subst.
      (* ADMIT: Weakening empty *)
      admit.
    + apply eqb_neq in Heqb as Hneq.
      inversion H. subst.
      eapply T_Var...
      simpl in H3.
      rewrite Heqb in H3...
  - (* TyAbs *)
    simpl.
    inversion H; subst.
    apply T_TyAbs; auto.
    eapply IHt...
    destr_eqb_eq s x.
    + (* ADMIT:
        (* t typeable without x, so also with x by weakening*)
      *)
      admit.
    + (* ADMIT: drop_ty_var s ((x, U)...) unfolds to goal*)
      admit.
  - (* LamAbs *)
    inversion H. subst.
    simpl.
    destruct (x =? s)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      apply T_LamAbs...
      (* ADMIT:  By H10: Delta,, (s, T1n) :: (s, U) :: Gamma |-+ t0 : T2n 
             and weakening *)
      admit.
    + apply eqb_neq in Heqb as Hneq.
      apply T_LamAbs...
      eapply IHt...
      (* ADMIT: By H10 and weakening swap/ cons permute *)
      admit.
  - (* Apply *)
    simpl.
    inversion H; subst.
    eapply T_Apply...
  - (* TyInst *)
     simpl.
     inversion H; subst.
     eapply T_TyInst...
(* ADMIT: See admits above*)
Admitted.

Definition gsubst (a : string) (T' : ty ) (Gamma : list (string * ty)) :=
  map (fun '(x, T) => (x, substituteT a T' T)) Gamma.

Lemma gsubst_empty : forall X U,
    gsubst X U nil = nil.
Proof.
  intros X U.
  unfold gsubst.
  simpl.
  reflexivity.
Qed.

Lemma gsubst__substituteT Gamma x X U T :
    lookup x Gamma = Datatypes.Some T ->
    lookup x (gsubst X U Gamma) = Datatypes.Some (substituteT X U T).
Proof with auto.
  induction Gamma.
  all: intros H; unfold gsubst.
  - inversion H.
  - destruct a.
    destruct (string_dec x s).
    + subst s.
      simpl.
      rewrite eqb_refl.
      rewrite lookup_eq in H.
      congruence.
    + rewrite lookup_neq in H...
      apply eqb_neq in n.
      rewrite eqb_sym in n.
      simpl.
      rewrite n...
Qed.

Lemma gsubst_absorbs_substituteT : forall x X U T Gamma,
    ((x, (substituteT X U T)) :: gsubst X U Gamma) = gsubst X U ((x, T) :: Gamma).
Proof.
  reflexivity.
Qed.


Lemma drop_ty_var__gsubst s X U Γ : 
  s <> X ->
  Ty.closed U ->
  drop_ty_var s (gsubst X U Γ) = gsubst X U (drop_ty_var s Γ).
Proof.
  intros Hneq Hclosed.
  unfold drop_ty_var.
  remember (nil) as R.
  clear HeqR.
  generalize dependent R.
  induction Γ; intros.
  - simpl.
    reflexivity.
  - destruct a as [x T].
    simpl.
    destruct (in_dec string_dec s
      (ftv
      (substituteT X U T))).
    + destruct (in_dec string_dec s (ftv T)).
      * eapply IHΓ.
      * exfalso.
        (* ADMIT: s in substT X U T, but U is closed, so s in T. *)
        admit.
    + 
      destruct (in_dec string_dec s (ftv T)).
      * exfalso.
        (* ADMIT: s not in substT X U T 
                  by s <> X, then s not in T *)
        admit.
      * destruct (in_dec string_dec x R).
        -- eapply IHΓ.
        -- rewrite <- gsubst_absorbs_substituteT.
           f_equal.
           eapply IHΓ.
(* ADMIT: See comments *)    
Admitted.

Lemma substituteT__normalisation T Tn SubTn X U:
  normaliser T = Some Tn ->
  normaliser (substituteT X U Tn) = Some SubTn ->
  normaliser (substituteT X U T) = Some SubTn.
Proof.
  (* I think this could be problematic if U has ftvs
    Let U = TyVar Z.

    We are substituting X.

    Let T = TyApp (TyLam X K (TyLam V K (TyVar V)) (X * V).
    Then Tn = TyLam V' K V'.

    substituteT X U T = TyApp (TyLam X K (TyLam V K (TyVar V)) (Z * V).
      normalises to
        TyLam V'' K (TyVar V'')
        where V'' is different fresh than V', because it is based on ftvs in U = Z <> X
    
    substitueT X U Tn = TyLam V' K V'


  *)
Admitted.

(* We need this lemma for open U by substA. Does it hold?*)
Lemma substituteT__normalisation2 T SubTn X U Un :
  normaliser U = Some Un ->
  normaliser (substituteT X U T) = Some SubTn ->
  normaliser (substituteT X Un T) = Some SubTn.
Proof.
  (*
    Suppose U = λ (P:K).   ((λ (Y:K). λ (V:K). V) * (P * V))
    Then Un = λ (P: K).     λ (V':K). (P * V)

    T = X * G

    substituteT X U T =   λ (P:K).   ((λ (Y:K). λ (V:K). V) * (P * V))   *  G
        ---> ((λ (Y:K). λ (V:K). V) * (G * V))
        ---> λ (V'':K). (G * V'')  

    substituteT X Un T = λ (P: K).     λ (V':K). (P * V)    *  G
        ---> λ (V':K). (G * V')

      (* Different V' and V''  !!!*)
  *)
Admitted.


(* We also know U is closed, but do not need it yet *)
Lemma commute_substituteT :
  forall X U V T,
    substituteT X U (substituteT X V T) = substituteT X (substituteT X U V) T.
Proof.
  intros X U V T.
  induction T.
  - simpl.
    destr_eqb_eq X s; auto.
    simpl.
    apply eqb_neq in H; rewrite H; auto.
  - simpl.
    destr_eqb_eq X s; auto.
    simpl.
    rewrite String.eqb_refl; auto.
    simpl.
    apply eqb_neq in H; rewrite H; auto.
    f_equal.
    apply IHT; auto.
  - simpl.
    f_equal.
    apply IHT1; auto.
    apply IHT2; auto.
  - simpl.
    destr_eqb_eq X s; auto.
    simpl.
    rewrite String.eqb_refl; auto.
    simpl.
    apply eqb_neq in H; rewrite H; auto.
    f_equal.
    apply IHT; auto.
  - simpl.
    f_equal.
    apply IHT1; auto.
    apply IHT2; auto.
Qed.

Theorem substA_preserves_typing :
    forall Delta Gamma X K U T Tn t,
    ((X, K) :: Delta) ,, Gamma |-+ t : T ->
    nil |-* U : K ->
    normaliser (substituteT X U T) = Some Tn ->
    Delta ,, (gsubst X U Gamma) |-+ ( :[X := U] t ): Tn.
Proof with (eauto using substituteT_preserves_kinding with typing).
  intros.
  generalize dependent Delta.
  generalize dependent Gamma.
  generalize dependent T.
  generalize dependent Tn.
  induction t.
  all: try (intros Tn T Hnorm__Tn Gamma Delta Htyp__t).
  all: try (inversion Htyp__t; subst).
  - (* Var *)
    simpl.
    (*
      lookup s Gamma = Some T0   (* T_Var*)
      normalise T0 T             (* T_Var *)

      normalise (substituteT X U T) Tn  (* P_Term *)
    *)
    apply T_Var with (T := (substituteT X U T0)).
    + eapply gsubst__substituteT; eauto.
    + eapply substituteT_preserves_kinding; eauto.
    + eapply substituteT__normalisation; eauto.
  - (* TyAbs *)
    simpl.
    destr_eqb_eq X s.
    + (* X = s *)
      simpl substituteT in Hnorm__Tn.
      rewrite eqb_refl in Hnorm__Tn.
      inversion Hnorm__Tn; subst.
      destruct_match.
      inversion H1; subst; clear H1.
      constructor.
      assert (Tn0 = t0).
      {
        (* ADMIT: has_type__normal*)
        admit.
      }
      subst.
      (* ADMIT: 
        t typeable without s,
        so the keys in Gamma that have values with s, are not
        free in t.
        so if we substitute s with U, then this does nothing
        still we can remove it then with drop_ty_var.
        see also annotationSubstitution.v
      *)
      admit.
    + simpl substituteT in Hnorm__Tn.
      apply eqb_neq in H.
      assert (X <> s) by now apply eqb_neq in H.
      rewrite H in Hnorm__Tn.
      inversion Hnorm__Tn; subst.
      destruct_match.
      inversion H3; subst; clear H3.
      constructor.
      rewrite drop_ty_var__gsubst; auto.
      * eapply IHt; eauto.
        (* ADMIT: Weakening swap *)
        admit.
      * (* ADMIT: U closed*)
        admit.
  - (* LamAbs *)
    simpl.
    simpl substituteT in Hnorm__Tn.
    inversion Hnorm__Tn; subst.
    repeat destruct_match.
    inversion H1; subst; clear H1.
    constructor; auto.
    * eapply substituteT_preserves_kinding; eauto.
    * eapply substituteT__normalisation; eauto.
    * assert ((s, substituteT X U T1n) :: gsubst X U Gamma = gsubst X U ((s, T1n) :: Gamma)).
      {
        rewrite gsubst_absorbs_substituteT; auto.
      }
      assert ( Hgsubst_not_normal :
        (s, (substituteT X U T1n)) :: (gsubst X U Gamma) = 
          (s, t1) :: gsubst X U Gamma).
      {
      (* ADMIT: substituteT X U T1n may not be normal, 
          how to reconcile? Must gsubst also normalise? 
          Maybe find counterexample tomorrow.

          Or does typing context not have to be normal?
          Something like, if it is well_typed for T in gamma,
          then it is well_typed for Tn in gamma.
          *)
          admit.
      }
      rewrite <- Hgsubst_not_normal.
      rewrite H.
      eapply IHt; eauto.
  - (* Apply *)
    simpl.
    assert (Delta |-* (substituteT X U T1n) : Kind_Base).
    {
      eapply substituteT_preserves_kinding; eauto.
      (* ADMIT: has_type base_kinded*)
      admit.
    }
      
    econstructor.
    2: {
      apply IHt2 with (T := T1n).
      (*ADMIT:  By strong normalization, this must exist*)
      - admit.
      - eauto.
    }
    + 
      eapply IHt1; eauto.
      simpl substituteT.
      (* ADMIT: By strong normalization, there is a type that
        substituteT X U T1n normalises to *)
      admit.
  - (* TyInst *)
    simpl.
    destr_eqb_eq X X0.
    + (* X = X0 *)
      assert (exists T1nn, normaliser T1n = Some T1nn) as [T1nn HT1nn].
      {
        (* ADMIT: strong normalization and T1n well-kinded*)
        admit.
      } 
      assert (exists subt0, normaliser (substituteT X0 U t0) = Some subt0) as [subt0 Hsubt0].
        {
          assert (((Delta) |-* (substituteT X0 U t0) : K2)).
          {
            apply substituteT_preserves_kinding with (L := K); auto.
            - (* ADMIT: Suppose X0 not in btv T1n, then by unfolding,
              suppose X0 in btv T1n, then by weakening*)
              admit.
          }
          (* ADMIT: strong normalization and substituteT X0 U t0 well-kinded*)
          admit.
      }

      econstructor.
      * eapply IHt; eauto.
        simpl substituteT.
        rewrite eqb_refl.
        simpl.
        rewrite HT1nn.
        reflexivity.
      * eapply substituteT_preserves_kinding; eauto.
        (* ADMIT: unfold or weakening, but also:
              btv T1nn subset of btv T1n by normalisation
              hence also by weakening.
        *)
        admit.
      * eauto.
      * (* t0 could be open?? Then T2n could be open?? *)
        rename t0 into T2.
        assert (T2 = T2n) by admit. clear H6. subst.
        assert (T1nn = T1n) by admit. clear HT1nn. subst.
        assert (T = (substituteT X0 T2n T1n)) by admit. clear H8. subst.
        erewrite commute_substituteT in Hnorm__Tn.
        (* substituteT X0 U T2n could be open, and T1n can as well, is that a problem?*)
        apply substituteT__normalisation2 with (U := substituteT X0 U T2n); eauto.
    + (* X <> X0 *)
      assert (exists subT1n, normaliser (substituteT X U t0) = Some subT1n) as [subT1n HsubT1n].
        {
          (* ADMIT: See above *)
          admit.
        }

      assert (exists SubT1nn, normaliser (substituteT X U T1n) = Some SubT1nn) as [SubT1nn HT1nn].
      {
        (* ADMIT: See above*)
        admit.
      } 

      econstructor.
      * eapply IHt; eauto.
        simpl substituteT.
        apply eqb_neq in H.
        rewrite H.
        simpl.
        rewrite HT1nn.
        constructor; eauto.
      * eapply substituteT_preserves_kinding; eauto.
        (* ADMIT: unfold or weakening, but also:
            btv SubT1nn subset of btv T1n by 
              normalisation and U closed!
            hence also by weakening.
        *)
        admit.
      * eauto.
      * 
        (* ADMIT: Something similar to above *)
        admit.
Admitted.


Theorem eval__type_preservation : forall t T v k,
    nil ,, nil |-+ t : T ->
    t =[k]=> v ->
    (nil ,, nil |-+ v : T).
Proof.
    intros t T v k Ht Hbs.
    generalize dependent T.
    induction Hbs; intros.
    - (* E_LamAbs *)
      exact Ht.
    - (* E_Apply *)
      inversion Ht; subst.
      specialize (IHHbs1 (Ty_Fun T1n T0) H4).
      inversion IHHbs1; subst.
      eapply IHHbs3.
      eapply substitution_preserves_typing; eauto.
      (* ADMIT: normaliser T = Some T1n, so T1n normal,
                     then by normalisation__stable
      *)
      admit.
    - (* E_TyAbs *)
      exact Ht.
    - (* E_TyInst *)
      inversion Ht; subst.
      specialize (IHHbs1 (Ty_Forall X0 K2 T1n) H2).
      inversion IHHbs1; subst.
      eapply IHHbs2.
      assert (nil = gsubst X0 T2 nil).
      {
        simpl.
        reflexivity.
      }
      rewrite H.
      eapply substA_preserves_typing; eauto.

      (* ADMIT: argument T2 normalizes to T2n, and then substituting the whole normalizes to T in assumption *)
      admit.
Admitted.