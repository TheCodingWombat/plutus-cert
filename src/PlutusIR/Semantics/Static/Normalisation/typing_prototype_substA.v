Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
From PlutusCert Require Import Analysis.BoundVars.

Require Export PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.Normalisation.Normalisation.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.PlutusIR.Semantics.Static.Builtins.Signatures.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Export PlutusCert.PlutusIR.Analysis.FreeVars.
From PlutusCert Require Import Dynamic.AnnotationSubstitution.

Require Import micromega.Lia. (* Importing the module for lia tactic *)

From PlutusCert Require Import 
    Normalisation.Normalisation 
    Norm_sound_complete
    PlutusIR 
    Util.List
    Static.Util
    Equality
    Kinding.Checker
    Util
    Dynamic.AnnotationSubstitution
    SubstituteTCA
    Size.

From PlutusCert Require Import alpha.util.

Import Coq.Lists.List.
Import ListNotations.
Import Coq.Strings.String.
Local Open Scope string_scope.

Inductive term :=
  | Var      : name -> term
  | LamAbs   : binderName -> ty -> term -> term
  | TyAbs    : binderTyname -> kind -> term -> term.



Fixpoint substA (X : string) (U : ty) (t : term) {struct t} : term :=
  match t with
  | Var y =>
      Var y
  | LamAbs bx T t0 =>
      LamAbs bx (substituteT X U T) (substA X U t0)
  | TyAbs bX K t0 =>
      if X =? bX
        then TyAbs bX K t0
        else TyAbs bX K (substA X U t0)
  end.


Function size (t : term) : nat :=
    1 +
    match t with
        | Var n           => 0
        | LamAbs n ty t   => size t
        | TyAbs n k t     => size t
    end.


Local Open Scope list_scope.

Inductive FreshOver : string -> list string -> Prop :=
  | FreshOver_nil : forall fr, FreshOver fr []
  | FreshOver_cons : forall fr x xs, ~ In fr (x :: xs) -> FreshOver fr xs -> FreshOver fr (x :: xs).

Reserved Notation "Delta ',,' Gamma '|-+' t ':' T" (at level 101, t at level 0, T at level 0, no associativity).
Inductive has_type : list (string * kind) -> list (string * ty) -> term -> ty -> Prop :=
  | T_Var : forall Γ Δ x T Tn K,
      lookup x Γ = Coq.Init.Datatypes.Some T ->
      Δ |-* T : K -> (* Added *)
      normalise T Tn ->
      Δ ,, Γ |-+ (Var x) : Tn
  | T_LamAbs : forall Δ Γ x T1 t T2n T1n,
      Δ |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Δ ,, (x, T1n) :: Γ |-+ t : T2n ->
      Δ ,, Γ |-+ (LamAbs x T1 t) : (Ty_Fun T1n T2n)
  | T_TyAbs : forall Δ Γ X K t Tn Y,
    (* TODO: Rename in Γ!*)
      FreshOver Y (map fst Δ) -> (* Do we need more? prolly term/gamma?*)
      ((Y, K) :: Δ) ,, Γ |-+ (substA X (Ty_Var Y) t) : Tn ->
      Δ ,, Γ |-+ (TyAbs X K t) : (Ty_Forall Y K Tn)

  where "Δ ',,' Γ '|-+' t ':' T" := (has_type Δ Γ t T).

Definition KB := Kind_Base.
Definition KB2 := Kind_Base.

Opaque KB.
Opaque KB2.
Definition KAB := Kind_Arrow Kind_Base Kind_Base.

Example TyAbsLamAbsEx :
  nil ,, nil |-+ (TyAbs "X" KB (LamAbs "v" (Ty_Var "X") (Var "v"))  ) : 
    (Ty_Forall "Y" KB (Ty_Fun (Ty_Var "Y") (Ty_Var "Y"))).
Proof.
  constructor.
  { constructor.
  (* freshness *) }
  simpl.
  constructor.
  - simpl. constructor. simpl. auto.
  - constructor.
  - eapply T_Var. simpl. eauto. constructor. simpl. eauto. constructor.
Qed.

(* This shows we must not rename in Gamma!*)
Example TyAbsDouble :
  nil ,, nil |-+ (TyAbs "X" KB (LamAbs "v" (Ty_Var "X")
                        (TyAbs "X" KB2 (LamAbs "w" (Ty_Var "X") (Var "v"))))  ) :
      (Ty_Forall "X" KB (Ty_Fun (Ty_Var "X") 
                        (Ty_Forall "Y" KB2 (Ty_Fun (Ty_Var "Y") (Ty_Var "X"))))).
Proof.
  constructor.
  { constructor.
  (* freshness *) }
  simpl.
  constructor.
  - simpl. constructor. simpl. auto.
  - constructor.
  - constructor.
    { constructor. intros Hcontra. inversion Hcontra. simpl in H. inversion H. inversion H. constructor. }
    simpl.
    constructor.
    + constructor. simpl. auto.
    + constructor.
    + eapply T_Var with (T := (Ty_Var "X")) (K := KB).
      * simpl. auto.
      * constructor. simpl. auto.
      * constructor.
Qed.
      

(*
type_check ((x, K)::nil) (v, Ty_Var x) (Var v) = Some (Ty_Var x).

type_check ((y, K)::nil) (v, Ty_Var x) (Var v) = Some (Ty_Var y).
*)

Definition fresh28 (Δ : list (string * kind)) : string := 
  "a" ++ String.concat EmptyString (map fst Δ).

Lemma fresh28_fresh_over_Δ : forall Δ,
  FreshOver (fresh28 Δ) (map fst Δ).
Proof.
Admitted.

Lemma substA_Var_same_size : forall x y t,
    size (substA x (Ty_Var y) t) = size t.
Proof.
Admitted.


From Equations Require Import Equations.
    
Equations? type_check (Δ : list (binderTyname * kind)) 
                     (Γ : list (binderName * ty)) 
                     (t : term) : option ty 
  by wf (size t) lt :=

  type_check Δ Γ (Var x) => 
    match lookup x Γ with
    | Some T => normaliser_Jacco Δ T
    | None => None
    end;
  type_check Δ Γ (LamAbs x T1 t0) =>
    match normaliser_Jacco Δ T1 with
    | Some T1n =>
        match kind_check Δ T1 with
        | Some Kind_Base =>
            match type_check Δ ((x, T1n) :: Γ) t0 with
            | Some T2 => Some (Ty_Fun T1n T2)
            | None => None
            end
        | _ => None
        end
    | None => None
    end;
  type_check Δ Γ (TyAbs X K t) =>
    let Y := fresh28 Δ in
    (* TODO: Rename in Γ!*)
    match type_check ((Y, K) :: Δ) Γ (substA X (Ty_Var Y) t) with
    | Some T => Some (Ty_Forall Y K T)
    | None => None
    end.


Proof.
all: intros; simpl; try lia.
- rewrite substA_Var_same_size. lia.
Qed.

Inductive AlphaVar : list (string * string) -> string -> string -> Prop :=
| alpha_var_refl x : AlphaVar [] x x
| alpha_var_cons z w sigma :
    AlphaVar ((z, w) :: sigma) z w
| alpha_var_diff x y z w sigma :
    x <> z -> 
    y <> w -> 
    AlphaVar sigma z w -> 
    AlphaVar ((x, y) :: sigma) z w.

Inductive Aty : list (string * string) -> ty -> ty -> Prop :=
| aty_var x y R : 
    AlphaVar R x y -> 
    Aty R (Ty_Var x) (Ty_Var y)
| aty_forall x y A s1 s2 R :
    Aty ((x, y) :: R) s1 s2 -> 
    Aty R (Ty_Forall x A s1) (Ty_Forall y A s2).

(* terms are Aterm related if their types are Aty related*)
Inductive Aterm : list (string * string) -> term -> term -> Prop :=
| Aterm_var x R : 
    Aterm R (Var x) (Var x)  (* We are only talking about alpha equivalence at type level*)
| Aterm_lamabs x T1 T2 t1 t2 R :
    Aty R T1 T2 -> 
    Aterm R t1 t2 -> 
    Aterm R (LamAbs x T1 t1) (LamAbs x T2 t2) (* these x are on term-level, they need not change*)
| Aterm_tyabs x y K t1 t2 R :
    Aterm ((x, y) :: R) t1 t2 -> 
    Aterm R (TyAbs x K t1) (TyAbs y K t2).

(* Contextual alpha equivalence: kinding contexts that match alpha contexts*)
Inductive CAlpha : list (string * string) -> list (string * PlutusIR.kind) -> list (string * PlutusIR.kind) -> Prop :=
  | calpha_nil D : CAlpha [] D D 
  | calpha_cons x y K R Δ Δ' :
    CAlpha R Δ Δ' ->
    CAlpha ((x, y)::R) ((x, K)::Δ) ((y, K)::Δ').

(* Currently sequential, do we want that? *)
Definition renTs (R : list (string * string)) (T : ty) : ty :=
  msubstT (map (fun p => (fst p, Ty_Var (snd p))) R) T.

(* Contextual alpha equivalence: type contexts that match alpha contexts*)

Inductive CΓAlpha : list (string * string) -> list (string * ty) -> list (string * ty) -> Prop :=
  | cΓalpha_nil R : CΓAlpha R nil nil
  | cΓalpha_cons x T R Γ Γ' :
    CΓAlpha R Γ Γ' ->
    CΓAlpha R ((x, T)::Γ) ((x, renTs R T)::Γ'). (* parallel or sequential?! *)

Require Import Coq.Program.Equality.

Lemma type_checking_preserves_alpha : forall x y K Δ Δ' Γ Γ' t t' T T' R,
    Aterm  ((x, y)::R) t t' ->
    CAlpha ((x, y)::R) ((x, K)::Δ) ((y, K)::Δ') ->
    Aty    ((x, y)::R) T T' ->
    CΓAlpha R Γ Γ' ->
    type_check ((x, K)::Δ) Γ t = Some T ->
    type_check ((y, K)::Δ') Γ' t' = Some T'.
Proof.
  (* Idk where/how yet, but I am pretty confident that we also need to rename types in Γ*)
  intros.
  dependent induction H.
  - autorewrite with type_check. autorewrite with type_check in H3.
    destruct_match; subst.
    (* Hmm. If we can find x0 in Γ, then it must already have ben in Δ? So x <> x0?
      This seems like an implicit invariant on the relation between Γ and Δ.
    *)

    (* x0 is a term variable, they are not renamed by type-alpha, hence *)
    assert (
      (* lookup x0 Γ = Some t -> CΓAlpha R Γ Γ' ->  *)
      (exists t', (lookup x0 Γ' = Some t') /\ (Aty R t t')))%type.
    {
      admit.
    }
    destruct H as [t' [Hlookup Ha_t']].
    rewrite Hlookup.
  - 
Admitted.

(* EASY: By construction. *)
Lemma CAlpha_id : forall Δ,
    CAlpha (map (fun z => (z, z)) (map fst Δ)) Δ Δ.
Admitted.


(* WRONG: Take Γ = (Ty_Var "x") and t = Var "v" ... *)
Lemma Delta_rename_preserves_type_checking : forall Δ Γ t T (x y : string) (K : kind),
    FreshOver y (map fst Δ) -> (* TODO: fresh over type variables in t and T?*)
    type_check ((x, K)::Δ) Γ t = Some T -> 
    type_check ((y, K)::Δ) Γ (substA x (Ty_Var y) t) = Some (substituteT x (Ty_Var y) T).
Proof.
  intros.
  remember ((map (fun z => (z, z)) (map fst Δ))) as R.
  eapply type_checking_preserves_alpha with (R := R); eauto.
  -
    (* R are identities, so it is alphaRename on term level
      I think this only holds if y is fresh over all type variables (bound/fresh) and variables in t.
      Since substA is non-capture-avoiding, we must not have that y is equal to a binder, then we would 
      have capture.
    *)
    admit.
  - constructor.
    rewrite HeqR.
    apply CAlpha_id.
  - admit.
  - 
    (* R are identities, so it just alphaRename with (x, y)!
      Suppose T = Ty_Lam y K (Ty_Var x), then of course we cannot rename x to y.
      Suppose T = Ty_App x y, then of course we cannot rename x to y.
      Hence y must be fresh over ftv T AND btv T

      Hence, this is exactly the alphaRename lemma (but for Plutus types, instead of ASTLC).
    *)
    admit.  
Admitted.

(* Not right. Take Γ = (Ty_Var "x") and t = Var "v" ... *)
Lemma Delta_rename_binder : forall Δ Γ t T (x y z : string) (K : kind),
    (* FreshOver y (map fst Δ) -> TODO: fresh over type variables in t and T? *)

    (* z,y not in Gamma? z, y not in Delta? *)
    type_check ((y, K)::Δ) Γ (substA x (Ty_Var y) t) = Some T -> 
    type_check ((z, K)::Δ) Γ (substA x (Ty_Var z) t) = Some (substituteT y (Ty_Var z) T).
Proof.
Admitted.



Require Import Coq.Arith.Wf_nat.

Require Import Coq.Program.Equality.

(* Induction hypothesis strengthened by well founded inductino on size of terms*)
Theorem type_checking_sound : 
 forall Δ Γ t T, type_check Δ Γ t = Some T -> (Δ ,, Γ |-+ t : T).
Proof with (try apply kind_checking_sound; try eapply normaliser_Jacco_sound; eauto).
    intros.
    remember (size t) as n.
    generalize dependent t.
    generalize dependent T.
    generalize dependent Δ.
    generalize dependent Γ.
    induction n using lt_wf_ind.
    intros.
    induction t; intros.
    - autorewrite with type_check in H0.
      destruct_match.
      pose proof (normaliser_Jacco__well_kinded _ _ _ H0) as [K H1].
      eapply T_Var; eauto.
      eapply normaliser_Jacco_sound; eauto.
    - autorewrite with type_check in H0.
      repeat destruct_match; subst.
      inversion H0; subst; clear H0.
      pose proof (normaliser_Jacco__well_kinded _ _ _ Heqo) as [K H1].
      eapply kind_checking_sound in Heqo0.
      eapply T_LamAbs; eauto.
      + apply normaliser_Jacco_sound in Heqo. auto.
      + eapply H; eauto.
        simpl. lia.
    - autorewrite with type_check in H0.
      simpl in H0.
      destruct_match.
      inversion H0; subst. clear H0.
      constructor.
      + apply fresh28_fresh_over_Δ.
      + eapply H; eauto.
        rewrite substA_Var_same_size. simpl. lia.
Qed.
    
Theorem type_checking_complete : 
 forall Δ Γ t T, (Δ ,, Γ |-+ t : T) -> exists T', type_check Δ Γ t = Some T' /\ Aty nil T T'.
Proof with (try apply kind_checking_complete; try eapply normaliser_Jacco_complete; eauto).
    intros.
    (* remember (size t) as n.
    generalize dependent t.
    generalize dependent T.
    generalize dependent Δ.
    generalize dependent Γ.
    induction n using lt_wf_ind. *)
    (* intros. *)
    induction H; intros; simpl.
    - autorewrite with type_check.
      rewrite H.
      exists Tn.
      split.
      + eapply normaliser_Jacco_complete; eauto.
      + (* alpha_refl*)
        admit.
    - admit.
    - destruct IHhas_type as [T' [Heqn Ha]].
      eexists.

      autorewrite with type_check.
      simpl.
      eapply Delta_rename_binder in Heqn.
      rewrite Heqn.
      split.
      eauto.
      constructor.
      (* substituteT rename*)
      admit.
      apply fresh28_fresh_over_Δ.

Admitted.



