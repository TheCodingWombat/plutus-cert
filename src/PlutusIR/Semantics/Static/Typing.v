Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
From PlutusCert Require Import Analysis.BoundVars.
From PlutusCert Require Import Analysis.FreeVars.

Require Export PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.Normalisation.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.PlutusIR.Semantics.Static.Builtins.Signatures.

Import Coq.Lists.List.
Import ListNotations.
Import Coq.Strings.String.
Local Open Scope string_scope.

(* Common built-in types *)
Definition Ty_Int := Ty_Builtin DefaultUniInteger.
Definition Ty_Bool := Ty_Builtin DefaultUniBool.
Definition Ty_String := Ty_Builtin DefaultUniString.
Definition Ty_Unit := Ty_Builtin DefaultUniUnit.
Definition Ty_BS := Ty_Builtin DefaultUniByteString.

Definition Ty_BinOp t := Ty_Fun t (Ty_Fun t t).
Definition Ty_BinPred t := Ty_Fun t (Ty_Fun t Ty_Bool).

(** Types of builtin functions *)
Definition lookupBuiltinTy f := to_ty (to_sig f).


(** Helper funcitons*)
Definition flatten {A : Type} (l : list (list A)) := List.concat (rev l).

Open Scope list_scope.
Lemma flatten_cons {A} x (xs : list (list A)) :
  flatten (x :: xs) = flatten xs ++ x.
Proof.
  unfold flatten. simpl.
  rewrite concat_app. simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Definition fromDecl (tvd : tvdecl) : string * kind :=
  match tvd with
  | TyVarDecl v K => (v, K)
  end.

Definition freshUnwrapIFix (F : ty) : string :=
  "a" ++ String.concat EmptyString (FreeVars.Ty.ftv F).

Definition unwrapIFix (F : ty) (K : kind) (T : ty) : ty :=
  let b := freshUnwrapIFix F in
  (Ty_App (Ty_App F (Ty_Lam b K (Ty_IFix F (Ty_Var b)))) T).

(* Main property of fresh variables: they are fresh*)
Lemma freshUnwrapIFix__fresh F :
  ~ In (freshUnwrapIFix F) (FreeVars.Ty.ftv F).
Admitted.

(** Typing of terms *)
Reserved Notation "Delta ',,' Gamma '|-+' t ':' T" (at level 101, t at level 0, T at level 0, no associativity).
Reserved Notation "Delta '|-ok_c' c ':' T" (at level 101, c at level 0, T at level 0).
Reserved Notation "Delta ',,' Gamma  '|-oks_nr' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-oks_r' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-ok_b' rec # b" (at level 101, b at level 0, no associativity).

Local Open Scope list_scope.

(* ************* drop_ty_var ************* *)

(*
Should have
drop_ty_var "s" (("x", Ty_Bool) :: ("x", Ty_Var "s") :: ("x", Ty_Int) :: nil) = nil

We keep an accumulator of already "removed" vars like "x"
*)
Fixpoint drop_ty_var' X (Γ : list (string * ty)) (acc : list string): list (string * ty) :=
  match Γ with
  | nil => nil
  | (x, T) :: Γ' =>
      if (in_dec string_dec X (Ty.ftv T)) then 
        drop_ty_var' X Γ' (x::acc)
      else if in_dec string_dec x acc then
        drop_ty_var' X Γ' acc
      else (x, T) :: drop_ty_var' X Γ' acc
  end.

Definition drop_ty_var X (Γ : list (string * ty)) : list (string * ty) :=
  drop_ty_var' X Γ nil.

Lemma drop_ty_var__inclusion X Γ :
  List.inclusion (drop_ty_var X Γ) Γ.
Proof.
  unfold List.inclusion.
  intros x v Hl.
  induction Γ.
  - inversion Hl.
  - simpl.
    destruct a as [a1 a2].
    (* TODO: destr_eqb_eq tactic *)
    destruct (string_dec a1 x); subst.
    + rewrite String.eqb_refl.
      f_equal.
      (* Suppose X in a2. Then by Hl
        we have that a2 <> v

        But then by drop_ty_var, all keys "x" will be removed from Hl,
        hence contradiction, because then it would have been None.

        Hence we must have X not in a2.
        Then by Hl we have lookup x ((x, a2)::...) = Some v => a2 = v
      *)
      admit.
    + rewrite <- String.eqb_neq in n.
      rewrite n.
      (* a1 <> x
        lookup x (drop ((a1, a2)::Γ) = Some v)
        Well, it is not the first one (a1), and the result is Some v.
        Hence we must have lookup x (drop Γ) = Some v. (possibly with even smaller Gamma, if a2 contains X)
        since drop Γ is a subset of Γ, we must have then also lookup x Γ = Some v.
      *)

Admitted.

Lemma drop_ty_var__inclusion_preserving : forall X Γ Γ',
    List.inclusion Γ Γ' -> List.inclusion (drop_ty_var X Γ) (drop_ty_var X Γ').
Proof.
intros X Γ Γ' Hincl.
unfold List.inclusion in Hincl.
unfold List.inclusion.
intros x v Hl.
(* by contradiction:
  Suppose lookup x (drop_ty_var X Γ') = None

    By drop_ty_var__inclusion,
      we have lookup x Γ' = Some v.

      then
        (x, v) in Gamma' and X in v (not possible by Hl)
      OR
        (x, v') in Gamma' and X in v', then also (x, v) gets removed

        But if this (x, v') occured to the right of (x, v), then still (x, v) in Gamma
        If it occurred to the left, we would have had
        lookup x Γ' = Some v' with v <> v'. Contradiction.
*)
Admitted.

Lemma drop_ty_var__lookup_some : forall X Γ x T,
    lookup x (drop_ty_var X Γ) = Some T ->
    exists T', lookup x Γ = Some T'.
(* Drop ty var cannot remove anything, so we cannot get None
  we are not guaranteed to get the same, as (x, S(X)) could be dropped and in front of (x, T).
*)
Admitted.

Definition inb_string (x : string) (xs : list string) : bool :=
  if in_dec string_dec x xs then true else false.

Lemma inb_string_true_iff (x : string) (xs : list string) :
  inb_string x xs = true <-> In x xs.
Proof.
  unfold inb_string.
  destruct (in_dec string_dec x xs); split; intro H; try easy; try congruence.
Qed.

Lemma inb_string_false_iff (x : string) (xs : list string) :
  inb_string x xs = false <-> ~ In x xs.
Proof.
  unfold inb_string.
  destruct (in_dec string_dec x xs); split; intro H; try easy; try congruence.
Qed.

Definition drop_Δ' (Δ : list (string * kind)) (bsn : list string) : list (string * kind) :=
  (* Just negb and In, but for bools isntead of props*)
  filter (fun x => negb (inb_string (fst x) bsn)) Δ.

Definition drop_Δ (Δ : list (string * kind)) (bs : list binding) : list (string * kind) :=
  (* Just negb and In, but for bools isntead of props*)
  drop_Δ' Δ (btvbs bs).

Lemma drop_Δ_nil : forall Δ,
    drop_Δ Δ nil = Δ.
Proof.
  intros Δ.
  unfold drop_Δ.
  induction Δ.
  - simpl. reflexivity.
  - simpl. f_equal.
    auto.
Qed.

From Coq Require Import Bool.

Lemma drop_Δ__weaken : forall Δ b bs,
  drop_Δ Δ (b::bs) = drop_Δ (binds_Delta b ++ Δ) (b::bs).
Proof.
  intros Δ b bs; unfold drop_Δ.
  induction b.
  - simpl. reflexivity.
  - simpl. destruct t.
    unfold drop_Δ'.
    remember (fun x : string * kind => _) as f.

    assert (Hf_nil: filter f [(b, k)] = []).
    {
      subst; simpl.
      assert (Hin: (inb_string b (btvbs (TypeBind (TyVarDecl b k) t0 :: bs))) = true).
      {
        unfold btvbs; simpl.
        rewrite inb_string_true_iff.
        apply in_eq.
      }
      rewrite Hin; auto.
    }
    assert (Hf_app: filter f Δ = filter f [(b, k)] ++ filter f Δ).
    {
      rewrite Hf_nil.
      rewrite app_nil_l.
      reflexivity.
    }
    rewrite Hf_app.
    rewrite filter_app; auto.
  - simpl. destruct d. destruct t.
    unfold drop_Δ'.
    remember (fun x : string * kind => _) as f.
    assert (Hf_nil: filter f [(b0, k)] = []).
    {
      subst; simpl.
      assert (Hin: (inb_string b0 (btvbs (DatatypeBind (Datatype (TyVarDecl b0 k) l b l0) :: bs))) = true).
      {
        unfold btvbs; simpl.
        rewrite inb_string_true_iff.
        apply in_eq.
      }
      rewrite Hin; auto.
    }
    assert (Hf_app: filter f Δ = filter f [(b0, k)] ++ filter f Δ).
    {
      rewrite Hf_nil.
      rewrite app_nil_l.
      reflexivity.
    }
    rewrite Hf_app.
    rewrite filter_app; auto.
Qed.


Lemma drop_Δ__unfold : forall Δ b bs,
  drop_Δ Δ (b::bs) = drop_Δ (drop_Δ Δ bs) [b].
Proof.
  intros Δ b bs.
  induction Δ.
  - simpl. reflexivity.
  - simpl.
    destruct (inb_string (fst a) (btvbs (b :: bs))) eqn:Heqn1.
    + (* a = b or In a (btvb bs)*)
      simpl.
      destruct (inb_string (fst a) (btvbs bs)) eqn:Heqn2.
      * (* a in bs *)
        simpl.
        apply IHΔ.
      * (* a notin bs, so then a = b*)
        simpl.
        assert (inb_string (fst a) (btvbs [b]) = true ).
        {
          rewrite btvbs_cons in Heqn1.
          rewrite inb_string_true_iff in Heqn1.
          rewrite in_app_iff in Heqn1. 
          destruct Heqn1 as [Heqn1 | Heqn1].
          - rewrite <- inb_string_true_iff in Heqn1.
            unfold btvbs; simpl.
            rewrite app_nil_r.
            assumption.
          - rewrite <- inb_string_true_iff in Heqn1.
            rewrite Heqn1 in Heqn2.
            inversion Heqn2.
        }
        simpl.
        rewrite H.
        simpl.
        apply IHΔ.
    + (* ~ In a (btvbs (b :: bs))*)
      assert (
        (inb_string (fst a) (btvbs bs)) = false).
      {
        rewrite btvbs_cons in Heqn1.
        rewrite inb_string_false_iff in Heqn1.
        rewrite not_in_app in Heqn1.
        destruct Heqn1 as [_ Heqn1].
        rewrite <- inb_string_false_iff in Heqn1.
        assumption.
      }
      rewrite H.
      simpl.
      assert ((inb_string (fst a) (btvbs [b])) = false).
      {
        rewrite btvbs_cons in Heqn1.
        rewrite inb_string_false_iff in Heqn1.
        rewrite not_in_app in Heqn1.
        destruct Heqn1 as [Heqn1 _].
        rewrite <- inb_string_false_iff in Heqn1.
        unfold btvbs. simpl.
        rewrite app_nil_r.
        assumption.
      }
      rewrite H0; simpl.
      f_equal.
      apply IHΔ.
Qed.

Lemma drop_Δ_nil__kinding : forall Δ T K,
    drop_Δ Δ nil |-* T : K -> Δ |-* T : K.
Proof.
  intros.
  rewrite drop_Δ_nil in H.
  assumption.
Qed.
    
  Lemma drop_Δ'__lookup_None : forall Δ xs x,
    In x (xs) -> lookup x (drop_Δ' Δ xs) = None.
  Proof.
    intros Δ xs x Hbtvbs.
    induction Δ; simpl.
    - reflexivity.
    - destruct a as [a1 a2]; simpl.
      destruct (negb (inb_string a1 (xs))) eqn:Heqn.
      + destruct (string_dec a1 x).
        * subst.
          exfalso.
          rewrite negb_true_iff in Heqn.
          rewrite inb_string_false_iff in Heqn.
          contradiction.
        * simpl.
          rewrite <- String.eqb_neq in n.
          rewrite n.
          exact IHΔ.
    + assumption.
  Qed.

  Lemma drop_Δ__lookup_None : forall Δ bs x,
    In x (BoundVars.btvbs bs) -> lookup x (drop_Δ Δ bs) = None.
  Proof.
    intros.
    unfold drop_Δ.
    eapply drop_Δ'__lookup_None.
    assumption.
  Qed.

   Lemma lookup_None__drop_Δ' : forall Δ xs x,
    ~ In x xs ->
    lookup x (drop_Δ' Δ xs) = lookup x Δ.
  Proof.
    intros Δ xs x HnotBtvb.
    induction Δ; simpl.
    - reflexivity.
    - destruct a as [a1 a2]; simpl.
      destruct ((inb_string a1 xs)) eqn:Heqn; simpl.
      + destruct (string_dec a1 x).
        * subst.
          rewrite inb_string_true_iff in Heqn.
          contradiction.
        * rewrite <- String.eqb_neq in n.
          rewrite n.
          rewrite IHΔ; auto.
      + simpl.
        destruct (string_dec a1 x).
        * subst.
          rewrite String.eqb_refl.
          reflexivity.
        * rewrite <- String.eqb_neq in n.
          rewrite n.
          rewrite IHΔ; auto. 
  Qed.

  Lemma lookup_None__drop_Δ : forall Δ bs x,
    ~ In x (BoundVars.btvbs bs) ->
    lookup x (drop_Δ Δ bs) = lookup x Δ.
  Proof.
    intros.
    unfold drop_Δ.
    eapply lookup_None__drop_Δ'.
    assumption.
  Qed.

  Lemma lookup_Some__drop_Δ'_no_xs : forall Δ xs x K,
    lookup x (drop_Δ' Δ xs) = Some K ->
    ~ In x xs.
  Proof.
    intros Δ xs x K Hl.
    induction Δ; simpl in *.
    - inversion Hl.
    - destruct a as [a1 a2]; simpl in *.
      destruct (inb_string a1 xs) eqn:Heqn; simpl in *.
      + destruct (string_dec a1 x).
        * apply IHΔ.
          assumption.
        * subst.
          apply IHΔ.
          exact Hl.
      + simpl in Hl.
        destruct (string_dec a1 x).
        * subst.
          rewrite inb_string_false_iff in Heqn.
          assumption.
        * rewrite <- String.eqb_neq in n.
          rewrite n in Hl.
          apply IHΔ.
          assumption.
  Qed.

  Lemma lookup_Some__drop_Δ_no_btvbs : forall Δ bs x K,
    lookup x (drop_Δ Δ bs) = Some K ->
    ~ In x (BoundVars.btvbs bs).
  Proof.
    intros.
    unfold drop_Δ.
    eapply lookup_Some__drop_Δ'_no_xs; eauto.
  Qed.

  Lemma drop_Δ'__inclusion : forall Δ xs,
    List.inclusion (drop_Δ' Δ xs) Δ.
  Proof.
    intros.
    induction Δ; simpl.
    - unfold List.inclusion; auto.
    - destruct a as [a1 a2].
      destruct (inb_string (fst (a1, a2)) xs) eqn:Heqn; simpl in *.
      + unfold inclusion.
        intros x v Hl.
        destruct (string_dec a1 x).
        * subst.
          exfalso.
          rewrite inb_string_true_iff in Heqn.
          eapply drop_Δ'__lookup_None in Heqn.
          rewrite Hl in Heqn.
          inversion Heqn.
        * simpl.
          rewrite <- String.eqb_neq in n.
          rewrite n.
          apply IHΔ.
          assumption.
      + unfold inclusion.
        intros x v Hl.
        destruct (string_dec a1 x).
        * subst.
          inversion Hl.
          rewrite String.eqb_refl.
          simpl.
          rewrite String.eqb_refl.
          reflexivity.
        * simpl.
          rewrite <- String.eqb_neq in n.
          rewrite n.
          apply IHΔ.
          simpl in Hl.
          rewrite n in Hl.
          assumption.
  Qed.

  Lemma drop_Δ__inclusion : forall Δ bs,
    List.inclusion (drop_Δ Δ bs) Δ.
  Proof.
    intros.
    unfold drop_Δ.
    eapply drop_Δ'__inclusion.
  Qed.


Lemma drop_Δ_cons__inclusion : forall Δ b bs,
    List.inclusion (drop_Δ Δ (b::bs)) (drop_Δ (binds_Delta b ++ Δ) bs).
Proof.
  intros Δ b bs.
  assert (Hweaken: drop_Δ Δ (b::bs) = drop_Δ (binds_Delta b ++ Δ) (b::bs)).
  {
    apply drop_Δ__weaken.
  }
  rewrite Hweaken; clear Hweaken.
  assert (Hunfold: drop_Δ (binds_Delta b ++ Δ) (b::bs) = drop_Δ (drop_Δ (binds_Delta b ++ Δ) bs) [b]).
  {
    apply drop_Δ__unfold.
  }
  rewrite Hunfold; clear Hunfold.
  apply drop_Δ__inclusion.
Qed.

  Lemma drop_Δ'__preserves__inclusion : forall Δ Δ' xs,
      List.inclusion Δ Δ' ->
      List.inclusion (drop_Δ' Δ xs) (drop_Δ' Δ' xs).
  Proof.
    intros Δ Δ' xs Hincl.
    unfold inclusion in *.
    intros x v Hl.
    assert (lookup x Δ' = Some v).
    {
      apply drop_Δ'__inclusion in Hl.
      apply Hincl in Hl.
      assumption.
    }
    assert ( ~ In x xs).
    {
      eapply lookup_Some__drop_Δ'_no_xs; eauto.
    }

    induction Δ'.
    - inversion H.
    - eapply lookup_None__drop_Δ' in H0; eauto.
      rewrite H0.
      assumption.
  Qed.

  Lemma drop_Δ__preserves__inclusion : forall Δ Δ' bs,
      List.inclusion Δ Δ' ->
      List.inclusion (drop_Δ Δ bs) (drop_Δ Δ' bs).
  Proof.
    intros.
    unfold drop_Δ.
    eapply drop_Δ'__preserves__inclusion.
    assumption.
  Qed.

Lemma btvbs_eq__drop_Δ_eq : forall Δ bs bs',
  btvbs bs = btvbs bs' ->
  drop_Δ Δ bs = drop_Δ Δ bs'.
Proof.
  intros Δ bs bs' Hbtvbs.
  unfold drop_Δ.
  rewrite Hbtvbs.
  reflexivity.
Qed.

Inductive has_type : list (string * kind) -> list (string * ty) -> term -> ty -> Prop :=
  (* Simply typed lambda caclulus *)
  | T_Var : forall Γ Δ x T Tn,
      lookup x Γ = Coq.Init.Datatypes.Some T ->
      Δ |-* T : Kind_Base ->
      normalise T Tn ->
      Δ ,, Γ |-+ (Var x) : Tn
  | T_LamAbs : forall Δ Γ x T1 t T2n T1n,
      Δ |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Δ ,, (x, T1n) :: Γ |-+ t : T2n ->
      Δ ,, Γ |-+ (LamAbs x T1 t) : (Ty_Fun T1n T2n)
  | T_Apply : forall Δ Γ t1 t2 T1n T2n,
      Δ ,, Γ |-+ t1 : (Ty_Fun T1n T2n) ->
      Δ ,, Γ |-+ t2 : T1n ->
      Δ ,, Γ |-+ (Apply t1 t2) : T2n
  (* Universal types *)
  | T_TyAbs : forall Δ Γ X K Y t Tn,
      ((X, K) :: Δ) ,, (drop_ty_var X (drop_ty_var Y Γ)) |-+ t : Tn ->
      ~ In Y (Ty.ftv Tn) -> (* This is absolutely required. Example Tn = ( X Y), then we cannot substitute X for Y and get an alhpa equivalent term
          (also not capture avoidingly) and*)
      ~ In Y (Ty.btv Tn) -> (* 
          This is an alternative to substituteTCA 
          I dont think it is problematic, we do not evautate the tyabs body, except when applying it
          using Tyinst.
          *)
      Δ ,, Γ |-+ (TyAbs X K t) : (Ty_Forall Y K (substituteT X (Ty_Var Y) Tn))
  | T_TyInst : forall Δ Γ t1 T2 T1n X K2 T0n T2n,
      Δ ,, Γ |-+ t1 : (Ty_Forall X K2 T1n) ->
      Δ |-* T2 : K2 ->
      normalise T2 T2n ->
      normalise (substituteTCA X T2n T1n) T0n ->
      Δ ,, Γ |-+ (TyInst t1 T2) : T0n
  (* Recursive types *)
  | T_IWrap : forall Δ Γ F T M K Tn Fn T0n,
      Δ |-* T : K ->
      normalise T Tn ->
      Δ |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      normalise F Fn ->
      normalise (unwrapIFix Fn K Tn) T0n ->
      Δ ,, Γ |-+ M : T0n ->
      Δ ,, Γ |-+ (IWrap F T M) : (Ty_IFix Fn Tn)
  | T_Unwrap : forall Δ Γ M Fn K Tn T0n,
      Δ ,, Γ |-+ M : (Ty_IFix Fn Tn) ->
      Δ |-* Tn : K ->
      normalise (unwrapIFix Fn K Tn) T0n ->
      Δ ,, Γ |-+ (Unwrap M) : T0n
  (* Additional constructs *)
  | T_Constant : forall Δ Γ T a,
      Δ ,, Γ |-+ (Constant (ValueOf T a)) : (Ty_Builtin T)
  | T_Builtin : forall Δ Γ f T Tn,
      T = lookupBuiltinTy f ->
      normalise T Tn ->
      Δ ,, Γ |-+ (Builtin f) : Tn
  | T_Error : forall Δ Γ S Sn,
      Δ |-* S : Kind_Base ->
      normalise S Sn ->
      Δ ,, Γ |-+ (Error S) : Sn
  (** Let-bindings
      Note: The rules for let-constructs differ significantly from the paper definitions
      because we had to adapt the typing rules to the compiler implementation of type checking.
      Reference: The Haskell module PlutusIR.TypeCheck.Internal in the
      iohk/plutus/plutus-core/plutus-ir project.
  **)
  | T_Let : forall Δ Γ bs t Tn Δ_no_esc Δ' Γ' bsGn,
      Δ' = flatten (map binds_Delta bs) ++ Δ ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn ->
      Γ' = bsGn ++ Γ ->
      Δ ,, Γ |-oks_nr bs ->
      Δ' ,, Γ' |-+ t : Tn ->
      Δ_no_esc = drop_Δ Δ bs ->
      Δ_no_esc |-* Tn : Kind_Base ->
      Δ ,, Γ |-+ (Let NonRec bs t) : Tn
  | T_LetRec : forall Δ Γ bs t Tn Δ_no_esc Δ' Γ' bsGn,
      (* There can be no duplicate bound variables in a let-rec *)
      NoDup (btvbs bs) ->
      NoDup (bvbs bs) ->

      Δ' = flatten (map binds_Delta bs) ++ Δ ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn ->
      Γ' = bsGn ++ Γ->
      Δ' ,, Γ' |-oks_r bs ->
      Δ' ,, Γ' |-+ t : Tn ->
      Δ_no_esc = drop_Δ Δ bs ->
      Δ_no_esc |-* Tn : Kind_Base ->
      Δ ,, Γ |-+ (Let Rec bs t) : Tn

(* Constructors are well-formed if their result type equals the fully applied
 * datatype (e.g. Either a b), and all parameter types are well-kinded
*)
with constructor_well_formed : list (string * kind) -> vdecl -> ty -> Prop :=
  | W_Con : forall Δ x T Targs Tr Tres,
      (Targs, Tres) = splitTy T ->
      (* We don't check the well-kindedness of Tres, this happens in
         W_Data (since the kind context needs to be slightly larger) *)
      (forall Ta, In Ta Targs -> Δ |-* Ta : Kind_Base) ->
      Tres = Tr ->
      Δ |-ok_c (VarDecl x T) : Tr

with bindings_well_formed_nonrec : list (string * kind) -> list (string * ty) -> list binding -> Prop :=
  | W_NilB_NonRec : forall Δ Γ,
      Δ ,, Γ |-oks_nr nil
  | W_ConsB_NonRec : forall Δ Γ b bs bsGn,
      Δ ,, Γ |-ok_b NonRec # b ->
      map_normalise (binds_Gamma b) bsGn ->
      ((binds_Delta b) ++ Δ) ,, (bsGn ++ Γ) |-oks_nr bs ->
      Δ ,, Γ |-oks_nr (b :: bs)

with bindings_well_formed_rec : list (string * kind) -> list (string * ty) -> list binding -> Prop :=
  | W_NilB_Rec : forall Δ Γ,
      Δ ,, Γ |-oks_r nil
  | W_ConsB_Rec : forall Δ Γ b bs,
      Δ ,, Γ |-ok_b Rec # b ->
      Δ ,, Γ |-oks_r bs ->
      Δ ,, Γ |-oks_r (b :: bs)

with binding_well_formed : list (string * kind) -> list (string * ty) -> recursivity -> binding -> Prop :=
  | W_Term : forall Δ Γ s x T t Tn rec,
      Δ |-* T : Kind_Base ->
      normalise T Tn ->
      Δ ,, Γ |-+ t : Tn ->
      Δ ,, Γ |-ok_b rec # (TermBind s (VarDecl x T) t)
  | W_Type : forall Δ Γ X K T rec,
      Δ |-* T : K ->
      Δ ,, Γ |-ok_b rec # (TypeBind (TyVarDecl X K) T)
  | W_Data : forall Δ Γ dtd XK YKs matchFunc cs X Ys Δ' Δ_ns rec Tres,
      dtd = Datatype XK YKs matchFunc cs ->
      X = tvdecl_name XK ->
      Ys = map tvdecl_name YKs ->

      (* No duplicate bound type variables *)
      NoDup (X :: Ys) ->

      (* No duplicate constructor names*)
      NoDup (map vdecl_name cs) ->

      (* Well-formedness of constructors *)
      (* Constructor argument types may not use type variable with 
      datatype's name in NonRec case*)
      Δ_ns = match rec with
            | NonRec => drop_Δ' Δ [X]
            | Rec => Δ
            end ->
      Δ' = rev (map fromDecl YKs) ++ Δ_ns ->
      (* The constructor types are well-kinded *) 
      Tres = constrLastTyExpected dtd -> (* The expected result type for each constructor *)
      (forall c, In c cs -> Δ' |-ok_c c : Tres) ->

      (* The expected result type is well-kinded *)
      (* In the case that this DatatypeBind is in a let-rec, X will already be
       * in Δ, but it is not problematic to add it another time. It is needed
       * for non-recursive DatatypeBinds
       *)
      (fromDecl XK :: Δ') |-* Tres : Kind_Base ->

      Δ ,, Γ |-ok_b rec # (DatatypeBind dtd)

  where "Δ ',,' Γ '|-+' t ':' T" := (has_type Δ Γ t T)
  and  "Δ '|-ok_c' c ':' T" := (constructor_well_formed Δ c T)
  and "Δ ',,' Γ '|-oks_nr' bs" := (bindings_well_formed_nonrec Δ Γ bs)
  and "Δ ',,' Γ '|-oks_r' bs" := (bindings_well_formed_rec Δ Γ bs)
  and "Δ ',,' Γ '|-ok_b' rec # b" := (binding_well_formed Δ Γ rec b).

Scheme has_type__ind := Minimality for has_type Sort Prop
  with constructor_well_formed__ind := Minimality for constructor_well_formed Sort Prop
  with bindings_well_formed_nonrec__ind := Minimality for bindings_well_formed_nonrec Sort Prop
  with bindings_well_formed_rec__ind := Minimality for bindings_well_formed_rec Sort Prop
  with binding_well_formed__ind := Minimality for binding_well_formed Sort Prop.

Combined Scheme has_type__multind from
  has_type__ind,
  bindings_well_formed_nonrec__ind,
  bindings_well_formed_rec__ind,
  binding_well_formed__ind.

(* Cannot type faulty const function *)
Example const_shadowing T :
  (nil ,, nil |-+
    (TyAbs "X" Kind_Base
      (LamAbs "x" (Ty_Var "X")
        (TyAbs "X" Kind_Base
          (LamAbs "y" (Ty_Var "X")
            (Var "x"))))) : T) -> False.
Proof.
  intros.
  (* inversion H; subst.
  inversion H6; subst.
  simpl drop_ty_var in *.
  inversion H9; subst.
  inversion H10; subst.
  inversion H8; subst.
  simpl in H13.
  inversion H13; subst.
  simpl in H1.
  inversion H1. *)
Admitted.


Definition well_typed t := exists T, [] ,, [] |-+ t : T.

Lemma T_Let__cons Δ Γ Γ_b b bs t Tn :
  Δ ,, Γ |-ok_b NonRec # b ->
  drop_Δ Δ (b::bs) |-* Tn : Kind_Base -> (* Tn may not mention types bound in b (escaping) *)
  map_normalise (binds_Gamma b) Γ_b ->
  binds_Delta b ++ Δ ,, Γ_b ++ Γ |-+ (Let NonRec bs t) : Tn ->
  Δ ,, Γ |-+ (Let NonRec (b :: bs) t) : Tn
.
Proof.
  intros H_typing_b H_kind H_mn H_ty.
  inversion H_ty; subst.

  econstructor.
  - exact eq_refl.
  - unfold flatten.
    simpl.
    rewrite concat_app.
    simpl.
    rewrite app_nil_r.
    apply MN_app.
    + eassumption.
    + eassumption.
  - exact eq_refl.
  - econstructor.
    + assumption.
    + eassumption.
    + eassumption.
  - simpl.
    rewrite flatten_cons.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    assumption.
  - eauto. 
  - eauto.
Qed.

Lemma has_type__normal : forall Delta Gamma t T,
    Delta ,, Gamma |-+ t : T ->
    normal_Ty T.
Proof with eauto.
  induction 1; intros; eauto using normalise_to_normal...
  - inversion IHhas_type1; subst...
    inversion H1.
Admitted.


(* ↪ = \hookrightarrow *)
Reserved Notation "Δ1 ',,' Γ1 '|-' C ':' HTy ↪ T1"
  (at level 101, C at level 0, T1 at level 0, no associativity).

(* Typing rules for one-hole contexts *)
Inductive context_has_type : list (string * kind) -> list (string * ty) -> context -> ((list (string * kind)) * list (string * ty) * ty) -> ty -> Prop :=

  | T_C_Hole : forall Δ Γ Tn,
      normal_Ty Tn ->
      Δ ,, Γ |- C_Hole : (Δ, Γ, Tn) ↪ Tn

  | T_C_LamAbs : forall Δ1 Γ1 x T1 C Δ Γ Tn T2n T1n,
      Δ1 |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Δ1 ,, (x, T1n) :: Γ1 |- C                 : (Δ , Γ, Tn) ↪ T2n ->
      Δ1 ,,             Γ1 |- (C_LamAbs x T1 C) : (Δ , Γ, Tn) ↪ (Ty_Fun T1n T2n)

  | T_C_Apply_L : forall Δ1 Γ1 Δ Γ C t Tn T1n T2n,
      Δ1 ,, Γ1 |- C : (Δ , Γ, Tn) ↪ (Ty_Fun T1n T2n) ->
      Δ1 ,, Γ1 |-+ t : T1n ->
      Δ1 ,, Γ1 |- (C_Apply_L C t) : (Δ , Γ, Tn) ↪ T2n

  | T_C_Apply_R : forall Δ1 Γ1 Δ Γ C t Tn T1n T2n,
      Δ1 ,, Γ1 |-+ t : (Ty_Fun T1n T2n) ->
      Δ1 ,, Γ1 |- C : (Δ , Γ, Tn) ↪ T1n ->
      Δ1 ,, Γ1 |- (C_Apply_R t C) : (Δ , Γ, Tn) ↪ T2n

  where
    "Δ1 ',,' Γ1 '|-' C ':' Hty ↪ T1" := (context_has_type Δ1 Γ1 C Hty T1)
.

Lemma context_has_type__normal : forall Δ1 Γ1 C Δ Γ T T1,
    Δ1 ,, Γ1 |- C : (Δ , Γ, T) ↪ T1 ->
    normal_Ty T1.
Proof with eauto using normalise_to_normal.
  intros Δ1 Γ1 C Δ Γ T T1 Cty.
  induction Cty...

  (* C_App_L *)
  - inversion IHCty...
    (* NO_Neutral *)
    + inversion H0.

  (* C_App_R *)
  - apply has_type__normal in H.
    inversion H...
    (* NO_Neutral *)
    + inversion H0.
Qed.

(* Lemma context_has_type__hole_normal : forall Δ1 Γ1 C Δ Γ T T1,
    Δ1 ,, Γ1 |- C : (Δ , Γ, T) ↪ T1 ->
    normal_Ty T.
Proof.
  intros Δ1 Γ1 C Δ Γ T T1 Cty.
  Require Import Coq.Program.Equality.
  dependent induction Cty.
  all: eauto.
Qed. *)


(* Lemma context_has_type__fill C t Δ1 Γ1 Δ Γ T T1 :
  Δ1 ,, Γ1 |- C : (Δ, Γ, T) ↪ T1 ->
  Δ ,, Γ |-+ t : T ->
  Δ1 ,, Γ1 |-+ (context_fill C t) : T1.
Proof.
  intros H_C H_t.
  dependent induction H_C;
  eauto using has_type.
Qed. *)

Lemma context_comp__has_type
  Δ1 Γ1 C T1
  Δ2 Γ2 C' T2
  Δ Γ T :
    Δ1 ,, Γ1 |- C : (Δ2, Γ2, T2) ↪ T1 ->
    Δ2 ,, Γ2 |- C' : (Δ, Γ, T) ↪ T2 ->
    Δ1 ,, Γ1 |- (context_comp C C') : (Δ, Γ, T) ↪ T1
.
Admitted.

(* New typing rule is not enough. Same issue with LamAbs*)

Definition LamAbsT := (Ty_App (Ty_Var "γ") (Ty_Lam "α" Kind_Base (Ty_Var "α"))).

Definition t' := (TyAbs "β" Kind_Base
          (LamAbs "x" LamAbsT (* <-- must be * *)
            (Var "x"))).

Definition KA := (Kind_Arrow Kind_Base Kind_Base).

Definition t := TyAbs "γ" (Kind_Arrow KA Kind_Base)
                  (TyAbs "α" Kind_Base
                    (TyInst t' (Ty_Var "α"))
                  ).

(* This is what we shall instantiate γ with*)
Definition MyGam := (Ty_Lam "z" KA Ty_Int).

(* "β" could have been something fresh though!*)
Lemma t'_well_typed :
  [("γ", Kind_Arrow KA Kind_Base)],,[("x", Ty_Int)] |-+ t' : 
      (Ty_Forall "β" Kind_Base (Ty_Fun LamAbsT LamAbsT)).


Definition FR := (fresh "β" (Ty_Var "α") (Ty_Var "α")).
Definition LamAbsT_Fr := (Ty_App (Ty_Var "γ") (Ty_Lam FR Kind_Base (Ty_Var FR))).

Lemma t_well_typed :
  [],,[] |-+ t : (Ty_Forall "γ" (Kind_Arrow KA Kind_Base)
                               (Ty_Forall "α" Kind_Base
                                 (Ty_Fun LamAbsT_Fr LamAbsT_Fr))).
Proof.
  unfold t.
  assert ((Ty_Forall "α" Kind_Base (Ty_Fun LamAbsT_Fr LamAbsT_Fr)) = substituteT "γ" (Ty_Var "γ") ((Ty_Forall "α" Kind_Base (Ty_Fun LamAbsT_Fr LamAbsT_Fr)))) by admit.
  rewrite H.
  unfold KA.
  unfold t'.
  unfold LamAbsT_Fr.

  eapply T_TyAbs.
  - {
  assert ((Ty_Fun (Ty_App (Ty_Var "γ") (Ty_Lam FR Kind_Base (Ty_Var FR)))
  (Ty_App (Ty_Var "γ") (Ty_Lam FR Kind_Base (Ty_Var FR)))) = substituteT "α" (Ty_Var "α") ((Ty_Fun (Ty_App (Ty_Var "γ") (Ty_Lam FR Kind_Base (Ty_Var FR)))
  (Ty_App (Ty_Var "γ") (Ty_Lam FR Kind_Base (Ty_Var FR)))))) by admit.
  rewrite H0.
  eapply T_TyAbs.
  {
  unfold LamAbsT.
  eapply T_TyInst with (K2 := Kind_Base) (X := "β") (T1n := Ty_Fun LamAbsT LamAbsT).
  - assert (Ty_Fun LamAbsT LamAbsT = substituteT "β" (Ty_Var "β") (Ty_Fun LamAbsT LamAbsT)) by admit.
    rewrite H1.
    eapply T_TyAbs.
    {
      constructor.
      - repeat econstructor.
      - apply N_TyApp; repeat econstructor.
      - econstructor. simpl. eauto. unfold LamAbsT. econstructor. constructor. simpl. eauto. repeat econstructor. unfold LamAbsT. apply N_TyApp; repeat econstructor.
    }
    admit.
    admit.
  - simpl. constructor. simpl. eauto.
  - eauto.
  - unfold LamAbsT.
    autorewrite with substituteTCA.
    assert ("β" =? "γ" = false) by admit.
      rewrite H1.
      assert ("β" =? "α" = false) by admit.
      rewrite H2.
    assert (existsb (String.eqb "α") (TypeSubstitution.ftv (Ty_Var "α")) = true) by admit.
      rewrite H3.
      assert ("β" =? fresh "β" (Ty_Var "α") (Ty_Var "α") = false) by admit.
    constructor.
    + simpl.
      apply N_TyApp; repeat econstructor.
      unfold rename.
      simpl.
      unfold FR.
      autorewrite with substituteTCA.
      
      rewrite H4.
      constructor.
    + simpl.
      apply N_TyApp; repeat econstructor.
      simpl.
      unfold FR.
      unfold rename.
      simpl.
      autorewrite with substituteTCA.
      rewrite H4.
      constructor.

  }
  - admit.
  - admit.

  }
  - (* let's assume that we also have the old tyabs rule, this rule is to 
    prevent capture, but we cannot have it with id subst*) admit.
  - admit.
Admitted.

Lemma t_instantiated :
  [],,[] |-+ (TyInst (TyInst t MyGam) Ty_Int) : (Ty_Fun Ty_Int Ty_Int). 
Proof.
  (* Hmmm. Now no ftv in type anymore, so evaluation will go okay.
    Maybe when we start evaluating and we encounter a tylam, there can never be a neutral type there, because that would mean that
    there is a ftv in that type, that is either bound in a TyAbs (in which case we wouldnt evaluate its body), or it must be in the context
    but we only evaluate closed terms, so no context!
  *)

