From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import FreeVars.
From PlutusCert Require Import WellScoped.
From PlutusCert Require Import Util.
From PlutusCert Require Import Util.List.
From PlutusCert Require Import Analysis.BoundVars.

Require Import Lists.List.
Require Import Strings.String.
Import ListNotations.

Import FreeVars.Term.


Section Weakening.

  Lemma weaken_well_scoped_Ty {Δ Δ' τ} :
    Δ |-* τ ->
    Δ ⊆ Δ' ->
    Δ' |-* τ.
  Admitted.

  Lemma weaken_well_scoped Δ Δ' Γ Γ' t :
    Γ ⊆ Γ' ->
    Δ ⊆ Δ' ->
    Δ ,, Γ |-+ t ->
    Δ' ,, Γ' |-+ t.
  Admitted.

  Lemma weaken_well_scoped_binding Δ Δ' Γ Γ' b :
    subset Δ Δ' ->
    subset Γ Γ' ->
    Δ ,, Γ |-ws_ok_b b ->
    Δ' ,, Γ' |-ws_ok_b b
  .
  Admitted.

  Lemma weaken_nr Δ Δ' Γ Γ' bs :
    Δ ⊆ Δ' ->
    Γ ⊆ Γ' ->
    Δ ,, Γ |-ws_oks_nr bs ->
    Δ' ,, Γ' |-ws_oks_nr bs
  .
  Admitted.

  Lemma weaken_r Δ Δ' Γ Γ' bs :
    Δ ⊆ Δ' ->
    Γ ⊆ Γ' ->
    Δ ,, Γ |-ws_oks_r bs ->
    Δ' ,, Γ' |-ws_oks_r bs
  .
  Admitted.


End Weakening.

Create HintDb weakening.
Hint Resolve
  weaken_well_scoped_Ty
  weaken_well_scoped
  weaken_well_scoped_binding
  weaken_nr
  weaken_r
   : weakening.

Definition P_Term t :=
  ftv t ,, fv t |-+ t.

Definition P_Binding b := forall rec,
match rec with
  | NonRec => ftvb rec b ,, fvb rec b |-ws_ok_b b
  | Rec    => btvb b ++ ftvb rec b ,, bvb b ++ fvb rec b |-ws_ok_b b
end.


Lemma ftv_well_scoped_Ty τ : Ty.ftv τ |-* τ.
Proof.
  induction τ.
  all: rewrite Ty.ftv_equation.
  all: try (eauto 10 using well_scoped_Ty, weaken_well_scoped_Ty, subset_append_l, subset_append_r, subset_cons_remove, In_singleton, subset_refl).
Qed.


Lemma fv_ws_LamAbs x ty t :
  P_Term t ->
  P_Term (LamAbs x ty t).
Proof.
  intros IH_t.
  unfold P_Term in *.

  econstructor.
  {
    rewrite ftv_equation.
    eauto 10 using weaken_well_scoped_Ty, subset_append_r, subset_refl, ftv_well_scoped_Ty.
  }
  {
    rewrite fv_equation.
    rewrite ftv_equation.
    eauto using weaken_well_scoped, subset_cons_remove, subset_append_r, subset_refl, subset_append_l.
  }
Qed.


Lemma subset_combination : forall xs ys zs,
  zs ⊆ (xs ++ ys ++ (zs \ xs)).
Proof.
  intros.
  assert (zs ⊆ (xs ++ zs \ xs)) by (apply subset_remove_many_append).
  eauto using subset_trans with subset.
Qed.

Lemma P_Binding_P_Bindings bs :
  Forall P_Binding bs ->
  ftvbs ftvb NonRec bs ,, fvbs fvb NonRec bs
    |-ws_oks_nr bs.
Proof.
  intros H_bs.
  induction bs as [ | b bs].
  - constructor.
  - constructor.
    + apply Forall_inv in H_bs.
      unfold P_Binding in H_bs.
      specialize (H_bs NonRec).
      rewrite ftvbs_equation.
      rewrite fvbs_equation.

      eapply weaken_well_scoped_binding. 
      3: exact H_bs.
      all: auto with subset.
    + apply Forall_inv_tail in H_bs.
      rewrite ftvbs_equation, fvbs_equation.
      eapply weaken_nr.
      1, 2: eapply subset_combination.
      auto.
Qed.


Section LetRecLemmas.

  Lemma ftvbs_app (bs bs' : list binding) :
    ftvbs ftvb Rec (bs ++ bs')
    ⊆ ftvbs ftvb Rec (bs' ++ bs).
  Proof.
  Admitted.

  Lemma btvbs_app x (bs bs' : list binding) :
    x ∉ BoundVars.btvbs (bs ++ bs') ->
    x ∉ BoundVars.btvbs (bs' ++ bs).
  Admitted.

End LetRecLemmas.


Lemma free_vars_well_scoped :
  (forall t, P_Term t) /\ (forall b, P_Binding b).
Proof.
  apply term__multind with (P := P_Term) (Q := P_Binding).

  (* Let *)
  {
    intros.
    unfold P_Term.
    destruct rec.
    (* NonRec *)
    {
      econstructor.
      3: {
        rewrite ForallP_Forall in H.
        apply P_Binding_P_Bindings in H.
        eapply weaken_nr.
        3: apply H.
        {
          rewrite ftv_equation.
          auto with subset.
        }
        {
          rewrite fv_equation.
          auto with subset.
        }
      }

      1, 2: reflexivity.

      unfold P_Term in H0.
      rewrite ftv_equation.
      rewrite fv_equation.
      eapply weaken_well_scoped.
      3: apply H0.
      all : apply subset_rev_append_l', subset_combination.
    }

    (* Rec*)
    {
      econstructor; try reflexivity.
      (* |-ws_oks_r bs*)
      {
        assert (exists bs', bs = bs') by (exists bs; reflexivity).
        destruct H1 as [bs' H_bs'].
        remember 
          (rev (BoundVars.btvbs bs) ++ ftv (Let Rec bs t)) as Δ.
        remember (rev (BoundVars.bvbs bs) ++ fv (Let Rec bs t))
          as Γ.
        rewrite H_bs' in HeqΔ, HeqΓ.
        assert (H_ex : exists bs_init, bs' = bs_init ++ bs).
          { exists []. symmetry. assumption.
          }
        clear H_bs'.

        unfold P_Binding in H.

        induction bs as [ | b bs].
        all: subst Δ Γ.
        { constructor. }
        { constructor.
          {
            clear IHbs.
            rewrite ForallP_Forall in H. apply Forall_inv in H.
            unfold P_Binding in H.
            specialize (H Rec).

            eapply weaken_well_scoped_binding.
            3: apply H.
            - apply subset_or.
              intros x H_x_in.
              destruct (in_dec string_dec x (BoundVars.btvbs bs')).
              + left.
                rewrite <- in_rev.
                assumption.
              + right.
                rewrite ftv_equation.
                destruct H_ex as [bs_init H_bs_init].
                subst bs'.
                rewrite in_app_iff.
                left.
                apply ftvbs_app.
                rewrite <- app_comm_cons.
                rewrite ftvbs_equation.
                rewrite in_app_iff.
                left.
                rewrite <- in_remove_many.
                constructor.
                * rewrite <- In_append_or in H_x_in.
                  destruct H_x_in.
                  ** admit. (* contradiction H1 n *)
                  ** assumption.

                * rewrite app_comm_cons.
                  apply btvbs_app.
                  auto.
            - admit. (* similar to previous subgoal, but with fv *)
          }

          {
            rewrite ForallP_Forall in H.
            apply Forall_inv_tail in H.
            rewrite <- ForallP_Forall in H.
            specialize (IHbs H).
            clear H.

            assert (exists bs_init : list binding, bs' = bs_init ++ bs).
            {
              destruct H_ex.
              rewrite app_cons_app_app in H.
              rewrite app_assoc in H.
              eauto.
            }
            auto.
          }
        }
      }

      unfold P_Term in H0.
      admit. (* Similar reasoning to above admit *)
      }

  }

  (* Var *)
  {
    unfold P_Term.
    intros s.
    rewrite ftv_equation, fv_equation.
    constructor.
    apply In_singleton.
  }

  (* TyAbs *)
  {
    intros s k t H_t.
    unfold P_Term in *.
    econstructor.
    rewrite ftv_equation.
    rewrite fv_equation.
    eapply weaken_well_scoped.
    3: exact H_t.
    all: auto with subset.
  }

  (* LamAbs *)
  { apply fv_ws_LamAbs.
  }

  (* Apply *)
  { intros t H_t t' H_t'. 
    unfold P_Term in *.
    constructor.
    {
    rewrite ftv_equation, fv_equation.
    eapply weaken_well_scoped.
    3: exact H_t.
    all: auto with subset.
    }
    {
    rewrite ftv_equation, fv_equation.
    eapply weaken_well_scoped.
    3: exact H_t'.
    all: auto with subset.
    }
  }

  (* Constant *)
  { intros s.
    unfold P_Term.
    rewrite ftv_equation, fv_equation.
    destruct s.
    constructor.
  }

  (* Builtin*)
  admit.

  (* TyInst*)
  admit.

  (* Error *)
  admit.

  (* IWrap *)
  admit.

  (* Unwrap *)
  admit.

  (* Constr *)
  admit.

  (* Case *)
  admit.

  (* TermBind*)
  {
    intros s v t H_t.
    unfold P_Binding.
    intros rec.
    destruct rec, v.
    (* NonRec *)
    {
      rewrite ftvb_equation, fvb_equation.
      unfold P_Term in H_t.
      admit. (* weakening *)
    }
    (* Rec *)
    {
      unfold P_Term in H_t.
      rewrite fvb_equation, ftvb_equation.
      simpl.

      admit. (* weakening and a cons/remove lemma*)
    }
  }

  (* TypeBind *)
  {
    intros v ty.
    unfold P_Binding.
    intros rec. destruct rec, v.
    {
      rewrite ftvb_equation, fvb_equation.
      constructor.
      apply ftv_well_scoped_Ty.
    }
    {
      rewrite ftvb_equation, fvb_equation.
      constructor.
      apply (weaken_well_scoped_Ty (ftv_well_scoped_Ty _)).
      auto with subset.
    }
  }

  (* DatatypeBind *)
  {
    intros dtd.
    unfold P_Binding.
    intros rec.
    destruct dtd as [[τ k] vs m cs].
    destruct rec. 
    (* NonRec *)
    {
      rewrite ftvb_equation, fvb_equation.
      econstructor.
      reflexivity.
      intros c H_c_in.
      destruct c as [x T] eqn:H_c.
      constructor.
      apply (weaken_well_scoped_Ty (ftv_well_scoped_Ty _)).
      unfold ftvc. simpl.
      apply subset_append_l.
      induction cs.
      { contradiction.
      }
      {
        destruct H_c_in.
        {
        simpl.
        apply subset_append_r.
        subst a. simpl.
        apply subset_refl.
        }
        {
          simpl.
          apply subset_append_l.
          auto.
        }
      }

    }
    (* Rec *)
    {
      rewrite ftvb_equation, fvb_equation.
      econstructor.
      reflexivity.

      intros c H_c_in.
      destruct c as [x T] eqn:H_c.
      constructor.

      apply (weaken_well_scoped_Ty (ftv_well_scoped_Ty _)).
      apply subset_append_l.
      apply subset_append_l.
      unfold ftvc. simpl.

      (* Copy-paste from NonRec*)
      induction cs.
      { contradiction.
      }
      {
        destruct H_c_in.
        {
        simpl.
        apply subset_append_r.
        subst a. simpl.
        apply subset_refl.
        }
        {
          simpl.
          apply subset_append_l.
          auto.
        }
      }
    }

  }

Admitted.
