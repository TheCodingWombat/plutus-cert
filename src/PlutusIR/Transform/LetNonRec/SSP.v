Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Transform.LetNonRec.Spec.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PlutusCert.PlutusIR.Semantics.Static.

Import Utf8_core.

Require Import FunctionalExtensionality.


Definition P_CNR_Term t t' := ∀ Δ Γ T,
  has_type Δ Γ t T ->
  has_type Δ Γ t' T
.

Definition P_CNR_Bindings bs fs := ∀ Δ Γ t T Γ_bs,
  Δ ,, Γ |-oks_nr bs ->
  map_normalise (flatten (map binds_Gamma bs)) Γ_bs ->
  (flatten (map binds_Delta bs) ++ Δ) ,, (Γ_bs ++ Γ) |-+ t : T ->
  Δ ,, Γ |-+ (fold_right apply t fs) : T
.

Definition P_CNR_LetRec_compat bs bs' := ∀ Δ Γ,
  Δ ,, Γ |-oks_r bs ->
  Δ ,, Γ |-oks_r bs' /\
  map binds_Gamma bs = map binds_Gamma bs' /\
  map binds_Delta bs = map binds_Delta bs'
  .

Definition P_CNR_Binding b (f : term -> term) :=
(
  match b with
    | TermBind Strict (VarDecl v ty) t_bound => ∀ t_bound',
      f = (fun t_bs => Apply (LamAbs v ty t_bs) t_bound') ->
      P_CNR_Term t_bound t_bound'
      /\
      (∀ Δ Γ t T Γ_bs,
          Δ ,, Γ |-ok_b b ->
          map_normalise (binds_Gamma b) Γ_bs ->
          binds_Delta b ++ Δ ,, Γ_bs ++ Γ |-+ t : T ->
          Δ,, Γ |-+ (f t) : T
      )
    | _ => True
  end
)
.

Definition P_CNR_Binding_compat b b' := ∀ Δ Γ,
    Δ ,, Γ |-ok_b b ->
    Δ ,, Γ |-ok_b b' /\
    binds_Delta b = binds_Delta b' /\
    binds_Gamma b = binds_Gamma b'
.

Ltac inv_typing :=
  match goal with
  | H : has_type _ _ _ _ |- _ => inversion H
  | H : _ ,,  _ |-ok_b _ |- _ => inversion H
  end
.

Lemma mn_singleton_deterministic T Tn v Γ :
  normalise T Tn ->
  map_normalise [(v, T)] Γ ->
  Γ = [(v, Tn)].
Proof.
  intros H_n H_mn.
  inversion_clear H_mn.
  match goal with H : map_normalise [] _ |- _ => inversion_clear H end.
  f_equal. f_equal.
  eauto using normalisation__deterministic.
Qed.


Derive Inversion_clear inv_oks_nr_cons with
  (∀ Δ Γ b bs, Δ,, Γ |-oks_nr (b :: bs)).

Derive Inversion_clear inv_oks_r_cons with
  (∀ Δ Γ b bs, Δ,, Γ |-oks_r (b :: bs)).

Derive Inversion_clear inv_ok_b with
  (∀ Δ Γ b, Δ,, Γ |-ok_b b).

Derive Inversion_clear inv_T_Let with
  (∀ Δ Γ bs t T, Δ,, Γ |-+ (Let NonRec bs t) : T).

Derive Inversion_clear inv_T_LetRec with
  (∀ Δ Γ bs t T, Δ,, Γ |-+ (Let Rec bs t) : T).

(* Simplifies the pattern where there are two assumptions that normalise the
   same type *)
Ltac simplify_norm :=
  match goal with
    H : map_normalise [(_, ?ty)] ?Γ,
    H' : normalise ?ty _
    |- _ => idtac H H'; pose proof (mn_singleton_deterministic _ _ _ _ H' H); subst Γ
  end.

Theorem CNR_Term__SSP : ∀ t t',
  CNR_Term t t' ->
  P_CNR_Term t t'.
  Proof with (eauto with typing).
  apply CNR__multind with
    (P := P_CNR_Term)
    (P0 := P_CNR_Bindings)
    (P1 := P_CNR_Binding)
    (P2 := P_CNR_LetRec_compat)
    (P3 := P_CNR_Binding_compat)
  .
  (* Solve compat_ cases of CNR_Term and CNR_Binding_compat *)
  all: try (unfold P_CNR_Term, P_CNR_Binding_compat; intros; inv_typing ; solve [eauto with typing]).
  - (* CNR_LetNonRec *)
    intros ? ? ? ? _ IH_t_body _ IH_bs.
    unfold P_CNR_Term, P_CNR_Term, P_CNR_Bindings in *.
    intros Δ Γ T H_typing_let.

    inversion H_typing_let using inv_T_Let. intros ? ? ? ? ? ? ? H_t_body ?.
    apply IH_t_body in H_t_body as H_t_body'; clear H_t_body IH_t_body.
    subst.
    apply IH_bs in H_t_body'; assumption.

  - (* CNR_LetRec *)
    unfold P_CNR_Term, P_CNR_LetRec_compat.
    intros ? ? ? ? _ IH_t_body _ IH_bs ? ? ? H_typing.
    inversion H_typing using inv_T_LetRec. intros ? ? ? ? H_mn_bs ? H_bs H_t_body.
    specialize (IH_bs _ _ H_bs).
    destruct IH_bs as [H_bs' [H_eq_Gamma H_eq_Delta]].
    rewrite H_eq_Gamma in H_mn_bs.
    rewrite H_eq_Delta in *...

  - admit.
  - (* CNR_LetRec_nil *)
    unfold P_CNR_Bindings.
    intros.
    unfold flatten in *. simpl in *.
    match goal with H : map_normalise _ _ |- _ => inversion H; subst end.
    assumption.

  - (* P_CNR_Bindings (b :: bs) (f_b :: f_bs) *)
    intros ? ? ? ? H IH_b _ IH_bs.
    intros ? ? ? ? Γ_b_bs H_b_bs H_mn_b_bs H_t.
    simpl.
    unfold apply at 1.
    inversion H. subst.

    inversion H_b_bs using inv_oks_nr_cons. intros ? H_b ? ?.
    inversion H_b; subst.

    unfold P_CNR_Bindings, P_CNR_Binding in *.

    (* Simplify map_normalise assumptions *)
    simpl in *.
    simplify_norm.

    rewrite flatten_cons in H_mn_b_bs.
    apply map_normalise__app in H_mn_b_bs as [Γ_bs [Γ_b [H_mn_bs [H_mn_b ?]]]].
    subst Γ_b_bs.
    simplify_norm.

    rewrite <- app_assoc, flatten_cons, app_nil_r in H_t.
    simpl in H_t.

    specialize (IH_b _ eq_refl).
    destruct IH_b as [IH_t_bound _].
    unfold P_CNR_Term in IH_t_bound...

  - (* P_CNR_Binding *)
    intros ? ? ? ? H_CNR_Term IH_t_bound.
    unfold P_CNR_Binding.
    intros t_bound'' H_eq.
    (* work-around: use arbitrary term to conclude t_bound' = t_bound'' *)
    apply equal_f with (x := Constant (ValueOf DefaultUniBool true)) in H_eq.
    inversion H_eq.
    subst t_bound''.
    clear H_eq.
    split.
    + assumption.
    + intros ? ? ? ? ? H_b ?.
      simpl in *.
      inversion H_b; subst.
      simplify_norm...

  - (* CNR_LetRec_compat [] *)
    unfold P_CNR_LetRec_compat.
    intros.
    intuition.
  - (* CNR_LetRec_compat :: *)
    intros ? ? ? ? _ IH_b _ IH_bs.
    unfold P_CNR_LetRec_compat.
    intros ? ? H_oks_b_bs.
    unfold P_CNR_Binding_compat, P_CNR_LetRec_compat in *.
    inversion H_oks_b_bs using inv_oks_r_cons. intros H_b H_bs.

    specialize (IH_b _ _ H_b) as [? [H_eq_1 H_eq_2]].
    specialize (IH_bs _ _ H_bs) as [? [H_eq_3 H_eq_4]].

    repeat split.
    + eauto with typing.
    + simpl. rewrite H_eq_2, H_eq_3. reflexivity.
    + simpl. rewrite H_eq_1, H_eq_4. reflexivity.
Admitted.
