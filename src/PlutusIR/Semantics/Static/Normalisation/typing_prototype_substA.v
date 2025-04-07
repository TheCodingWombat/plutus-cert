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

Section term.

Fixpoint tv (t : term) : list string :=
  match t with
  | Var x => [] (* no type variables *)
  | LamAbs n T t0 => Ty.ftv T ++ Ty.btv T ++ tv t0 (* n is a term variable*)
  | TyAbs n K t0 => n :: (tv t0)
  end.

End term.

Definition tvΓ (Γ : list (binderName * ty)) : list string :=
  flat_map (fun x => (Ty.btv (snd x) ++ Ty.ftv (snd x))%list) Γ.

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
Inductive has_type : list (binderTyname * kind) -> list (binderName * ty) -> term -> ty -> Prop :=
  | T_Var : forall Γ Δ x T Tn K,
      lookup x Γ = Coq.Init.Datatypes.Some T ->
      Δ |-* T : K -> (* Added *)
      normalise T Tn ->
      Δ ,, Γ |-+ (Var x) : Tn
  | T_LamAbs : forall Δ Γ x T1 T1n t T2n,
      Δ |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Δ ,, (x, T1n) :: Γ |-+ t : T2n ->
      Δ ,, Γ |-+ (LamAbs x T1 t) : (Ty_Fun T1n T2n)
  | T_TyAbs : forall Δ Γ X K t Tn Y,
      FreshOver Y (map fst Δ ++ tvΓ Γ ++ tv t) -> (* TODO: may we choose a var that occurs as a term var? Think so*)
      ((Y, K) :: Δ) ,, Γ |-+ (substA X (Ty_Var Y) t) : Tn ->
      Δ ,, Γ |-+ (TyAbs X K t) : (Ty_Forall Y K Tn)

  where "Δ ',,' Γ '|-+' t ':' T" := (has_type Δ Γ t T).

(* May not be equal to btv because of capture, may not be equal to ftv because also capture
    TODO: what about type variables in Delta?
*)
Definition fresh28 (Δ : list (string * kind)) (Γ : list (string * ty)) (t : term): string := 
  "a" ++ String.concat EmptyString (map fst Δ ++ tvΓ Γ ++ tv t).

Definition KB := Kind_Base.
Definition KB2 := Kind_Base.

Opaque KB.
Opaque KB2.
Definition KAB := Kind_Arrow Kind_Base Kind_Base.

Example TyAbsLamAbsEx :
  nil ,, nil |-+ (TyAbs "X" KB (LamAbs "v" (Ty_Var "X") (Var "v"))  ) : 
    (Ty_Forall "Y" KB (Ty_Fun (Ty_Var "Y") (Ty_Var "Y"))).
Proof.
Admitted.

(* This shows we must not rename in Gamma!*)
Example TyAbsDouble :
  nil ,, nil |-+ (TyAbs "X" KB (LamAbs "v" (Ty_Var "X")
                        (TyAbs "X" KB2 (LamAbs "w" (Ty_Var "X") (Var "v"))))  ) :
      (Ty_Forall "X" KB (Ty_Fun (Ty_Var "X") 
                        (Ty_Forall "Y" KB2 (Ty_Fun (Ty_Var "Y") (Ty_Var "X"))))).
Proof.
Admitted.
      

(*
type_check ((x, K)::nil) (v, Ty_Var x) (Var v) = Some (Ty_Var x).

type_check ((y, K)::nil) (v, Ty_Var x) (Var v) = Some (Ty_Var y).
*)

Lemma fresh28_fresh_over_Δ : forall Δ Γ t,
  FreshOver (fresh28 Δ Γ t) (map fst Δ).
Proof.
Admitted.

Lemma fresh28_fresh_over_t : forall Δ Γ t,
  FreshOver (fresh28 Δ Γ t) (tv t).
Proof.
Admitted.

Lemma fresh28_fresh_over_Γ : forall Δ Γ t,
  FreshOver (fresh28 Δ Γ t) (tvΓ Γ).
Proof.
Admitted.

Lemma fresh28_fresh FreshOver : forall Δ Γ t,
  FreshOver (fresh28 Δ Γ t) (map fst Δ ++ tvΓ Γ ++ tv t).
Admitted.

Lemma substA_Var_same_size : forall x y t,
    size (substA x (Ty_Var y) t) = size t.
Proof.
Admitted.

Lemma FreshOver_app : forall x xs ys,
    FreshOver x (xs ++ ys) -> FreshOver x xs /\ FreshOver x ys.
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
      match kind_check Δ T1 with
      | Some Kind_Base =>
            match normaliser_Jacco Δ T1 with
              | Some T1n =>
                    match type_check Δ ((x, T1n) :: Γ) t0 with
                    | Some T2 => Some (Ty_Fun T1n T2)
                    | None => None
                    end
              | _ => None
            end
      | _ => None
      end;
  type_check Δ Γ (TyAbs X K t) =>
    let Y := fresh28 Δ Γ t in
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
  | aty_fun A1 A2 A3 A4 R :
      Aty R A1 A3 -> 
      Aty R A2 A4 -> 
      Aty R (Ty_Fun A1 A2) (Ty_Fun A3 A4)
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
Inductive AΔ : list (string * string) -> list (binderTyname * PlutusIR.kind) -> list (binderTyname * PlutusIR.kind) -> Prop :=
  | AΔ_nil D : AΔ [] D D 
  | AΔ_cons x y K R Δ Δ' :
    AΔ R Δ Δ' ->
    AlphaVar R x y ->
    AΔ R ((x, K)::Δ) ((y, K)::Δ').

(* Currently sequential, do we want that? *)
Definition renTs (R : list (string * string)) (T : ty) : ty :=
  msubstT (map (fun p => (fst p, Ty_Var (snd p))) R) T.

(* Contextual alpha equivalence: type contexts that match alpha contexts*)
Inductive AΓ : list (string * string) -> list (binderName * ty) -> list (binderName * ty) -> Prop :=
  | AΓ_nil R : AΓ R nil nil
  | AΓ_cons x T T' R Γ Γ' :
    AΓ R Γ Γ' ->
    Aty R T T' ->
    AΓ R ((x, T)::Γ) ((x, T')::Γ').

Lemma AΓ_refl : forall Γ,
    AΓ [] Γ Γ.
Admitted.

Lemma Aty_refl : forall T,
    Aty [] T T.
Admitted.

Lemma Aterm_refl : forall t,
    Aterm [] t t.
Proof.
  induction t.
  - constructor.
  - constructor; auto.
    apply Aty_refl.
  - constructor; auto.
    (* need to generalize over identity substitutions *)
Admitted.

Require Import Coq.Program.Equality.

Lemma AΓ_Some {R Γ Γ' x T} :
    AΓ R Γ Γ' ->
    lookup x Γ = Some T ->
    exists T', 
      Aty R T T' /\
      lookup x Γ' = Some T'.
Admitted.

Lemma AΓ_extend_fresh : forall Y Y' Γ Γ' R,
    FreshOver Y (tvΓ Γ) ->
    FreshOver Y' (tvΓ Γ') ->
    AΓ R Γ Γ' ->
    AΓ ((Y, Y')::R) Γ Γ'.
Admitted.

Lemma AΔ_extend_fresh : forall Y Y' Δ Δ' R,
    FreshOver Y (map fst Δ) ->
    FreshOver Y' (map fst Δ') ->
    AΔ R Δ Δ' ->
    AΔ ((Y, Y')::R) Δ Δ'.
Admitted.

Lemma normaliser_Jacco_alpha : forall Δ Δ' T T' Tn R,
    AΔ R Δ Δ' ->
    Aty R T T' ->
    normaliser_Jacco Δ T = Some Tn ->
    exists Tn',
      Aty R Tn Tn' /\
      normaliser_Jacco Δ' T' = Some Tn'.
  
  (* oof, but the lemmas about types and alpha are at the ASTLC level. 
    Maybe we can leave those open for now?
  *)
Admitted.

Lemma normalise_alpha : forall T T' Tn R,
    Aty R T T' ->
    normalise T Tn ->
    exists Tn',
      Aty R Tn Tn' /\
      normalise T' Tn'.
Admitted.

Lemma has_kind_alpha : forall Δ Δ' T T' K R,
    AΔ R Δ Δ' ->
    Aty R T T' ->
    Δ  |-* T : K ->
    Δ' |-* T' : K.
Admitted.

(* See alpha_rename.v*)
Lemma alpha_substA : forall x y t,
    ~ In y (tv t) ->
    Aterm ((x, y)::nil) t (substA x (Ty_Var y) t).
Admitted.

Lemma alpha_trans_rename_right b'' s s'' t t' R :
  FreshOver b'' (tv t') ->
  Aterm ((s, s'')::R) t t' ->
  Aterm ((s, b'')::R) t (substA s'' (Ty_Var b'') t').
Admitted.

Lemma alpha_trans_rename_left b'' s s'' t t' R :
  FreshOver b'' (tv t) ->
  Aterm ((s'', s)::R) t t' ->
  Aterm ((b'', s)::R) (substA s'' (Ty_Var b'') t) t'.
Admitted.

Lemma alpha_trans_rename_both b' b'' s' s'' t t' R :
  FreshOver b' (tv t) ->
  FreshOver b'' (tv t') ->
  Aterm ((s', s'')::R) t t' ->
  Aterm ((b', b'')::R) (substA s' (Ty_Var b') t) (substA s'' (Ty_Var b'') t').
Admitted.

Lemma type_checking_complete' : forall Δ Δ' Γ Γ' t t' T R,
    AΔ     R Δ Δ' ->
    AΓ     R Γ Γ' ->
    Aterm  R t t' ->
    has_type Δ Γ t T ->
    exists T',
      Aty R T T' /\
      type_check Δ' Γ' t' = Some T'.
Proof.
  intros.
  generalize dependent t'.
  generalize dependent Δ'.
  generalize dependent Γ'.
  generalize dependent R.
  induction H2.
  - intros R Γ' AΓ Δ' AΔ t' Ha.
    inversion Ha; subst.
    autorewrite with type_check.
    destruct (AΓ_Some AΓ H) as [T' [HaT' HlookupT']].
    rewrite HlookupT'.
    eapply normaliser_Jacco_complete in H1; eauto.
    eapply normaliser_Jacco_alpha; eauto.
  - intros R Γ' AΓ Δ' AΔ t' Ha.
    inversion Ha; subst.

    assert (exists T2_normalised, 
      Aty R T1n T2_normalised /\
      normalise T2 T2_normalised) as [T2_normalised [AT2 AT2norm]].
    {
      eapply normalise_alpha; eauto.
    }

    assert (exists T', Aty R T2n T' /\ type_check Δ' ((x, T2_normalised)::Γ') t2 = Some T') as [T' [HaT' HtcT']].
    {
      eapply IHhas_type; auto.
      constructor; auto.
    }

    exists (Ty_Fun T2_normalised T').
    split.
    constructor; auto.
    autorewrite with type_check.
    assert (has_kind Δ' T2 Kind_Base).
    { eapply has_kind_alpha; eauto. }
    assert (kind_check Δ' T2 = Some Kind_Base).
    { eapply kind_checking_complete; eauto. }
    rewrite H3.
    eapply normaliser_Jacco_complete in AT2norm; eauto.
    rewrite AT2norm.
    rewrite HtcT'.
    auto.
  - intros R Γ' AΓ Δ' AΔ t' Ha.
    inversion Ha; subst.
    remember (fresh28 Δ' Γ' t2) as Y'.
    assert (exists T', (Aty ((Y, Y')::R) Tn T') /\ 
      type_check ((Y', K)::Δ') Γ' (substA y (Ty_Var Y') t2) = Some T').
    {
      eapply IHhas_type.
      - apply AΓ_extend_fresh; auto. 
        + apply FreshOver_app in H as [_ H].
          apply FreshOver_app in H as [H _].
          auto.
        + rewrite HeqY'.
          eapply fresh28_fresh_over_Γ.
      - constructor. 
        apply AΔ_extend_fresh; auto.
        + apply FreshOver_app in H as [H _]; auto.
        + rewrite HeqY'. apply fresh28_fresh_over_Δ.
        + constructor.
      - eapply alpha_trans_rename_both; auto.
        + apply FreshOver_app in H as [_ H].
          apply FreshOver_app in H as [_ H']. auto.
        + rewrite HeqY'.
          eapply fresh28_fresh_over_t.
    }
    destruct H0 as [T' [At' HtcT']].
    exists (Ty_Forall Y' K T').
    split.
    + constructor. auto.
    + autorewrite with type_check.
      rewrite <- HeqY'.
      simpl.
      rewrite HtcT'.
      auto.
Qed.

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
      pose proof (normaliser_Jacco__well_kinded _ _ _ Heqo0) as [K H1].
      
      eapply T_LamAbs; eauto.
      + eapply kind_checking_sound; eauto.
      + apply normaliser_Jacco_sound in Heqo0. auto.
      + eapply H; eauto.
        simpl. lia.
    - autorewrite with type_check in H0.
      simpl in H0.
      destruct_match.
      inversion H0; subst. clear H0.
      constructor.
      + eapply fresh28_fresh.
      + eapply H; eauto.
        rewrite substA_Var_same_size. simpl. lia.
Qed.
    
Theorem type_checking_complete : 
 forall Δ Γ t T, (Δ ,, Γ |-+ t : T) -> exists T', Aty nil T T' /\ type_check Δ Γ t = Some T'.
Proof with (try apply kind_checking_complete; try eapply normaliser_Jacco_complete; eauto).
  intros.
  eapply type_checking_complete'; eauto.
  - constructor.
  - apply AΓ_refl.
  - apply Aterm_refl.
Qed.



