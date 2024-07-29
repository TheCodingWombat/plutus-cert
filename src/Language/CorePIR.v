From PlutusCert Require Import
  Language
  Language.PIR
  Language.GHC.Core.AST
  PlutusIR
  PlutusIR.Semantics.Dynamic.Bigstep
  .

Require Import Utf8_core.
Require Import Strings.String.


Inductive ctp : Expr string -> term -> Prop :=
  | ctp_app : ∀ s t s' t',
      ctp s s' ->
      ctp t t' ->
      ctp (App s t) (Apply s' t')

  | ctp_lam : ∀ x ty t t',
      ctp t t' ->
      ctp (Lam x t) (LamAbs x ty t')

  | ctp_var : ∀ (x : string),
      ctp (AST.Var x) (PlutusIR.Var x)

  | ctp_const_int : ∀ i nty ty,
      ctp
        (Lit (LitNumber nty i ty))
        (Constant (ValueOf DefaultUniInteger i))
  .

Notation "s ▷ t" := (ctp s t) (at level 60).

From PlutusCert Require Import Core.BigStep.

Module Core := Core.BigStep.
From PlutusCert Require Import PlutusIR.Semantics.Dynamic.Bigstep.
Module PIR := Dynamic.Bigstep.


Lemma subst_preserves_ctp : ∀ t1 t1' t2 t2' x,
  t1 ▷ t1' ->
  t2 ▷ t2' ->
  Core.subst x t1 t2 ▷ subst x t1' t2'.
Proof.
  intros ? ? ? ? ? H_ctp_t1 H_ctp_2.
  generalize dependent t2'.
  induction t2.
  all: intros t2' H_ctp_2; try inversion H_ctp_2; subst.

  (* Var*)
  - inversion H_ctp_2; subst.
    simpl.
    destruct (eqb x i); assumption.
  (* Constant *)
  - assumption.
  - simpl; eauto using ctp.
  - simpl.
    destruct (eqb x b);
    eauto using ctp.
Qed.

Require Import Coq.Program.Equality.
Lemma H : ∀ t t' r,
  ctp t t'      ->
  Core.eval t r ->
  ∃ n r', PIR.eval t' r' n
    /\ ctp r r' /\ ¬ is_error r'
.
Proof.
  intros t.
  intros t' r H_ctp H_eval_core.
  generalize dependent t'.
  dependent induction H_eval_core.
  all: intros; inversion H_ctp; subst.

  (* Lam *)
  - repeat eexists.
    all: eauto using eval.
    unfold not. inversion 1.

  (* Apply *)
  - rename s' into t1'.
    rename t'0 into t2'.

    specialize (IHH_eval_core1 _ H1) as [n1 [v1 [eval_t1' [ctp_v1 not_error1]]]].
    inversion ctp_v1; subst.
    specialize (IHH_eval_core2 _ H3) as [n2 [v2 [eval_t2' [ctp_v2 not_error2]]]].
    assert (
      ctp (Core.subst x vx b) (subst x v2 t')).
      { eauto using subst_preserves_ctp. }
    specialize (IHH_eval_core3 _ H) as [n3 [v3 [eval_subst ctp_subst]]].
    eexists.
    eexists.
    split.
    + econstructor. all: try eauto.
    + assumption.

  (* Literal *)
  -
    repeat eexists.
    + econstructor.
    + econstructor.
    + unfold not. inversion 1.
Qed.

Corollary ctp_fwd : ∀ t t' r,
  ctp t t'      ->
  Core.eval t r ->
  ∃ n r', PIR.eval t' r' n.
Proof.
  intros t t' r H_ctp H_eval.
  pose proof H.
  specialize (H _ _ _ H_ctp H_eval) as [n [r' [ H_pir_eval [H_ctp_r H_err]]]].
  repeat eexists.
  eauto.
Qed.

Lemma fwd : ∀ t t',
  t ▷ t' -> forward CoreLang PIRLang t t'.
Proof.
  intros t t' H_rel.
  unfold forward.
  intros n res.
  simpl.
  intros H_eval_core.

  assert ( H_ctp : app CoreLang t (const CoreLang n)
         ▷ app PIRLang  t' (const PIRLang  n)).
  {
    simpl.
    eauto using ctp.
  }

  pose proof H as ctp_fwd.
  specialize (ctp_fwd _ _ _ H_ctp H_eval_core) as [n' [r' [H_eval_pir [H_ctp_r _]]]].
  inversion H_ctp_r; subst.
  eexists.
  simpl in H_eval_pir.
  eassumption.
Qed.
