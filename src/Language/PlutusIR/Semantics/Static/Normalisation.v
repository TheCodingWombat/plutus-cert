Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Export PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.

(** Type equality *)
Reserved Notation "T1 '=b' T2" (at level 40).
Inductive EqT : Ty -> Ty -> Prop :=
  (* Beta-reduction *)
  | Q_Beta : forall X K T1 T2 T1',
      substituteTCA X T2 T1 = T1' ->
      Ty_App (Ty_Lam X K T1) T2 =b T1'
  (* Reflexivity, Symmetry and Transitivity*)
  | Q_Refl : forall T,
      T =b T
  | Q_Symm : forall T S,
      T =b S ->
      S =b T
  | Q_Trans : forall S U T,
      S =b U ->
      U =b T ->
      S =b T
  (* Congruence *)
  | Q_Fun : forall S1 S2 T1 T2,
      S1 =b S2 ->
      T1 =b T2 ->
      Ty_Fun S1 T1 =b Ty_Fun S2 T2
  | Q_Forall : forall X K S T,
      S =b T ->
      Ty_Forall X K S =b Ty_Forall X K T
  | Q_Lam : forall X K S T,
      S =b T ->
      Ty_Lam X K S =b Ty_Lam X K T
  | Q_App : forall S1 S2 T1 T2,
      S1 =b S2 ->
      T1 =b T2 ->
      Ty_App S1 T1 =b Ty_App S2 T2
  | Q_IFix : forall F1 F2 T1 T2,
      F1 =b F2 ->
      T1 =b T2 ->
      Ty_IFix F1 T1 =b Ty_IFix F2 T2
where "T1 '=b' T2" := (EqT T1 T2).

#[export] Hint Constructors EqT : core.

(** Normal types *)
Inductive normal_Ty : Ty -> Prop :=
  | NO_TyLam : forall bX K T,
      normal_Ty T ->
      normal_Ty (Ty_Lam bX K T)
  | NO_neutral : forall T,
      neutral_Ty T ->
      normal_Ty T
  | NO_TyFun : forall T1 T2,
      normal_Ty T1 ->
      normal_Ty T2 ->
      normal_Ty (Ty_Fun T1 T2)
  | NO_TyForall : forall bX K T,
      normal_Ty T ->
      normal_Ty (Ty_Forall bX K T)
  | NO_TyIFix : forall F T,
      normal_Ty F ->
      normal_Ty T ->
      normal_Ty (Ty_IFix F T)
  | NO_TyBuiltin : forall st,
      normal_Ty (Ty_Builtin st)

with neutral_Ty : Ty -> Prop :=
  | NE_TyVar : forall X,
      neutral_Ty (Ty_Var X)
  | NE_TyApp : forall T1 T2,
      neutral_Ty T1 ->
      normal_Ty T2 ->
      neutral_Ty (Ty_App T1 T2).

Scheme normal_Ty__ind := Minimality for normal_Ty Sort Prop
  with neutral_Ty__ind := Minimality for neutral_Ty Sort Prop.

Combined Scheme normal_Ty__multind from 
  normal_Ty__ind,
  neutral_Ty__ind.

#[export] Hint Constructors normal_Ty neutral_Ty : core.

(** Type normalisation *)
Inductive normalise : Ty -> Ty -> Prop :=
  | N_BetaReduce : forall bX K T1 T2 T1' T2' T,
      normalise T1 (Ty_Lam bX K T1') ->
      normalise T2 T2' ->
      normalise (substituteTCA bX T2' T1') T ->
      normalise (Ty_App T1 T2) T
  | N_TyApp : forall T1 T2 T1' T2',
      normalise T1 T1' ->
      neutral_Ty T1' ->
      normalise T2 T2' ->
      normalise (Ty_App T1 T2) (Ty_App T1' T2')
  | N_TyFun : forall T1 T2 T1' T2',
      normalise T1 T1' ->
      normalise T2 T2' ->
      normalise (Ty_Fun T1 T2) (Ty_Fun T1' T2')
  | N_TyForall : forall bX K T0 T0',
      normalise T0 T0' ->
      normalise (Ty_Forall bX K T0) (Ty_Forall bX K T0')
  | N_TyLam : forall bX K T0 T0',
      normalise T0 T0' ->
      normalise (Ty_Lam bX K T0) (Ty_Lam bX K T0')
  | N_TyVar : forall X,
      normalise (Ty_Var X) (Ty_Var X)
  | N_TyIFix : forall F T F' T',
      normalise F F' ->
      normalise T T' ->
      normalise (Ty_IFix F T) (Ty_IFix F' T')
  | N_TyBuiltin : forall st,
      normalise (Ty_Builtin st) (Ty_Builtin st)
  .

#[export] Hint Constructors normalise : core.

(** Properties of type normalisation *)
Lemma normalise_to_normal : forall T T_norm,
    normalise T T_norm ->
    normal_Ty T_norm.
Proof. 
  induction 1; eauto.
Qed.

Lemma normalisation__deterministic : forall T T_norm T'_norm,
    normalise T T_norm ->
    normalise T T'_norm ->
    T_norm = T'_norm.
Proof.
  intros.
  generalize dependent T'_norm.
  induction H; intros.
  - inversion H2.
    + subst.
      apply IHnormalise1 in H5. inversion H5. subst.
      apply IHnormalise2 in H6. subst.
      apply IHnormalise3; eauto.
    + subst.
      apply IHnormalise1 in H5. 
      inversion H5. subst.
      inversion H6.
  - inversion H2.
    + subst.
      apply IHnormalise1 in H5.
      inversion H5. subst.
      inversion H0.
    + subst.
      f_equal; eauto.
  - inversion H1. subst.
    f_equal; eauto.
  - inversion H0. subst.
    f_equal; eauto.
  - inversion H0. subst.
    f_equal; eauto.
  - inversion H0. subst.
    f_equal; eauto.
  - inversion H1. subst.
    f_equal; eauto.
  - inversion H0. subst.
    eauto.
Qed.

Ltac invert_normalise :=
  match goal with
  | H : normalise ?T ?T_norm |- _ => inversion H; subst; f_equal; eauto
  end.

Theorem normalisation__stable :
  (forall T, normal_Ty T -> (forall T_norm, normalise T T_norm -> T = T_norm)) /\
  (forall T, neutral_Ty T -> (forall T_norm, normalise T T_norm -> T = T_norm)).
Proof with eauto.
  eapply normal_Ty__multind; intros...
  all: try solve [invert_normalise].
  - inversion H3.
    + subst.
      eapply H0 in H6.
      subst.
      inversion H.
    + subst.
      f_equal...
Qed.

Theorem normalisation__sound : forall T T_norm,
    normalise T T_norm ->
    T =b T_norm.
Proof with eauto. induction 1... Qed.

Lemma normalisation__complete : forall S T S_norm,
    S =b T ->
    normalise S S_norm ->
    normalise T S_norm.
Proof. Abort.

(** Normalisation of lists of types*)
Inductive map_normalise : list (tyname * Ty) -> list (tyname * Ty) -> Prop :=
  | MN_nil : 
      map_normalise nil nil
  | MN_cons : forall X T Ts Tn Tsn,
      map_normalise Ts Tsn ->
      normalise T Tn ->
      map_normalise ((X, T) :: Ts) ((X, Tn) :: Tsn).

#[export] Hint Constructors map_normalise : core.

Require Import Coq.Lists.List.

Lemma map_normalise__app : forall l1 l2 ln,
    map_normalise (l1 ++ l2) ln ->
    exists l1n l2n, 
      map_normalise l1 l1n /\
      map_normalise l2 l2n /\
      ln = l1n ++ l2n.
Proof.
  induction l1; intros.
  - exists nil. exists ln. eauto.
  - inversion H. subst.
    eapply IHl1 in H2.
    destruct H2 as [l1n' [l2n' [Hmn1 [Hmn2 Heq]]]].
    subst.
    exists ((X, Tn) :: l1n').
    exists l2n'.
    eauto.
Qed.

Lemma map_normalise__deterministic : forall l ln ln',
    map_normalise l ln ->
    map_normalise l ln' ->
    ln = ln'.
Proof. Admitted.
