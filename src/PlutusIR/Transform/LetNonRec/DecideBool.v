From Coq Require Import
  String
  List
  Bool
  Program
  Datatypes
  Utf8_core
  PeanoNat
.

From PlutusCert Require Import
  Util
  Util.Tactics
  Util.List
  PlutusIR
  PlutusIR.Analysis.Equality
  PlutusIR.Transform.Compat
  PlutusIR.Transform.LetNonRec.Spec.

Import ListNotations.

(*
   Returns `Some t'` if bindings were desugared correctly, where t' is the rest
   of the desugared term.

   Note that dec_Term has to be passed manually. In this form, the
   termination checker is happy when checking dec_Term (it's probably
   inlining dec_Bindings within dec_Term, and then sees the structural
   recursive call to dec_Term.

   We want this as a separate definition so that proofs don't have to deal with
   a big (fix ...) expression. The termination checker doesn't allow it to be
   part of the mutual recursive binding group of dec_Term, so this is the
   workaround.

   Below is a specialized version dec_Bindings that you do not have to pass
   dec_Term.
*)

Section Bindings.

  Context (dec_Term : term -> term -> bool).

  Fixpoint bindings_to_apps (bs : list binding) : option (list (term -> term)) :=
    match bs with
      | []        => Some []
      | TermBind Strict (VarDecl v ty) rhs :: bs =>
          option_map
            (cons (fun t => Apply (LamAbs v ty t) rhs))
            (bindings_to_apps bs)
      |  _ => None
    end.

  Fixpoint dec_Bindings' (bs : list binding) (t : term) {struct bs} : option term :=
    match bs with
      | nil       => Some t
      | cons b bs => match b, t with
        | TermBind Strict (VarDecl v ty) rhs, Apply (LamAbs v' ty' body') rhs' =>
          if (String.eqb v v' && Ty_eqb ty ty' && dec_Term rhs rhs')
            then dec_Bindings' bs body'
            else None
        | _, _ => None
        end
    end.

End Bindings.

(*
  Returns true if the term was desugared correctly.
*)
Fixpoint dec_Term (x y : term) {struct x} : bool := match x, y with

  (* non-recursive bindings should be desugared *)
  | Let NonRec bs body, t =>
       match dec_Bindings' dec_Term bs t with
        | Some body' => dec_Term body body'
        | Nothing    => false
       end

  (* Other cases should be compatible, i.e. identical constructors
     and recursive Terms recursively desugared *)
  | Let Rec bs t   , Let Rec bs' t'     => forall2b dec_Binding_compat bs bs' && dec_Term t t'
  | Var n          , Var n'             => String.eqb n n'
  | TyAbs n k t    , TyAbs n' k' t'     => String.eqb n n' && Kind_eqb k k' && dec_Term t t'
  | LamAbs n ty t  , LamAbs n' ty' t'   => String.eqb n n' && Ty_eqb ty ty' && dec_Term t t'
  | Apply s t      , Apply s' t'        => dec_Term s s' && dec_Term t t'
  | Constant c     , Constant c'        => constant_eqb c c'
  | Builtin f      , Builtin f'         => func_eqb f f'
  | TyInst t ty    , TyInst t' ty'      => dec_Term t t' && Ty_eqb ty ty'
  | Error ty       , Error ty'          => Ty_eqb ty ty'
  | IWrap ty1 ty2 t, IWrap ty1' ty2' t' => Ty_eqb ty1 ty1' && Ty_eqb ty2 ty2' && dec_Term t t'
  | Unwrap t       , Unwrap t'          => dec_Term t t'
  | Constr i ts    , Constr i' ts'      => Nat.eqb i i' && forall2b dec_Term ts ts'
  | Case t ts      , Case t' ts'        => dec_Term t t' && forall2b dec_Term ts ts'

  | _, _ => false
  end
with dec_Binding_compat (b b' : binding) : bool := match b, b' with
  (* These cases are only used for recursive let-bindings, i.e.
     equal and recursive Terms should be desugared *)
  | TermBind s vdecl t, TermBind s' vdecl' t' => strictness_eqb s s' && VDecl_eqb vdecl vdecl' && dec_Term t t'
  | TypeBind tvdecl ty, TypeBind tvdecl' ty'  => TVDecl_eqb tvdecl tvdecl' && Ty_eqb ty ty'
  | DatatypeBind dtd  , DatatypeBind dtd'     => DTDecl_eqb dtd dtd'
  | _, _ => false
  end
.

(* See comment of dec_Bindings' *)
Definition dec_Bindings : list binding -> term -> option term := 
  dec_Bindings' dec_Term.


(*

Note [IH for nested datatypes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Usual IH used by `induction` tactic does not suffice, it only holds
for _direct_ subterms, and not for subterms within a list subterm.

- Define an induction/recursion scheme similarly to dec_Term above.
*)


(*

Note [Refactor VarDecl]
~~~~~~~~~~~~~~~~~~~~~~

VarDecl in Plutus is isomorphic to (string, Ty). Since plutus-cert currently
models Ty as unit, VarDecl is currently defined as string (for convenience).
This should of course change when Ty is taken into account.

This also means that in some cases, a proof or function may "invent" a Ty with
value tt : unit, where in a typed situation it should be part of an assumption
or argument.

*)

Definition P_Term t := ∀ t',
  dec_Term t t' = true <-> CNR_Term t t'.

Definition P_Binding_compat b :=  ∀ b',
    dec_Binding_compat b b' = true <-> CNR_Binding_compat b b'
.

Definition P_Binding_NonRec b := ∀ t t_inner,
  (∃ bs, dec_Bindings (b :: bs) t = Some t_inner) <->
  (∃ f fs,
    CNR_Binding b f /\
    fold_right apply t_inner (f :: fs) = t)
.

Definition P_Binding b :=
  P_Binding_compat b /\ P_Binding_NonRec b
.

Ltac simpl_dec_Term :=
  try match goal with (* Try because not used in Binding cases *)
    | H:dec_Term _ _ = true |- _ => simpl in H
  end;
  repeat (match goal with
    | H : match ?r with _ => _ end = true |- _ => destruct r
    | H : false = true |- _ => inversion H
    | H : _ && _ = true |- _ => rewrite andb_true_iff in H
    | H : _ /\ _ |- _ => destruct H in H
  end).

Ltac rewrite_reflection :=
  repeat (match goal with

    | H : String.eqb _ _ = true |- _ => rewrite String.eqb_eq in H
    | H : Kind_eqb _ _ = true |- _ => rewrite Kind_eqb_eq in H
    | H : Ty_eqb _ _ = true |- _ => rewrite Ty_eqb_eq in H
    | H : constant_eqb _ _ = true |- _ => rewrite constant_eqb_eq in H
    | H : func_eqb _ _ = true |- _ => rewrite func_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => rewrite Nat.eqb_eq in H
    | H : strictness_eqb _ _ = true |- _ => rewrite strictness_eqb_eq in H
    | H : VDecl_eqb _ _ = true |- _ => rewrite VDecl_eqb_eq in H
    | H : forall2b ?eqb ?xs _ = true,
      H_elems : ForallP _ ?xs |- _
        => rewrite ForallP_Forall in H_elems;
           rewrite (forall2b_Forall2_Forall _ _ dec_Term xs _ H_elems) in H

    | H : dec_Term ?t ?t' = true ,
      IH : _ -> dec_Term ?t _ = true <-> _ |- _ => rewrite IH in H
  end).


Ltac tac_fwd :=
  intros;
  simpl_dec_Term;
  rewrite_reflection;
  subst;
  auto using CNR_Term.


Ltac simpl_goal :=
  simpl;
  repeat (rewrite andb_true_iff)
.

Ltac bwd_reflection :=
  repeat (match goal with
    | |- String.eqb _ _ = true => rewrite String.eqb_eq; reflexivity
    | |- Kind_eqb _ _ = true   => rewrite Kind_eqb_eq; reflexivity
    | |- Ty_eqb _ _ = true   => rewrite Ty_eqb_eq; reflexivity
    | |- constant_eqb _ _ = true => rewrite constant_eqb_eq; reflexivity
    | |- func_eqb _ _ = true => rewrite func_eqb_eq; reflexivity
    | |- Nat.eqb _ _ = true => rewrite Nat.eqb_eq; reflexivity
    | |- strictness_eqb _ _ = true => rewrite strictness_eqb_eq; reflexivity
    | |- VDecl_eqb _ _ = true => rewrite VDecl_eqb_eq; reflexivity

    |
      H_elems : ForallP _ ?xs |- forall2b ?eqb ?xs _ = true =>
        rewrite ForallP_Forall in H_elems;
        rewrite (forall2b_Forall2_Forall _ CNR_Term dec_Term xs _ H_elems);
        assumption
    | IH : _ -> dec_Term ?t _ = true <-> _ |- dec_Term ?t _ = true => rewrite IH; assumption
  end).

Ltac tac_bwd :=
  inversion 1; subst;
  simpl_goal;
  repeat split;
  bwd_reflection.

Ltac dec_tac :=
  unfold P_Term, P_Binding;
  intros;

  (* Split cases, solve impossible ones *)
  match goal with t' : term |- _ =>
    destruct t'; split; try solve [inversion 1]
  end; [> tac_fwd | tac_bwd].

Definition desugar_fun v ty t_bound : term -> term :=
  fun t_inner => Apply (LamAbs v ty t_inner) t_bound.

Lemma dec_Bindings_exists : ∀ bs t t_inner,
  dec_Bindings bs t = Some t_inner ->
  (∃ fs, fold_right apply t_inner fs = t)
.
Proof.
  induction bs as [ | b bs].
  - simpl. intros. inversion H. subst t_inner.
    exists []. auto.
  - intros.
    destruct b;
    try solve [inversion H].
    destruct s; try solve [inversion H].
    destruct v.
    simpl in H.
    destruct t; try solve [inversion H].
    destruct t2; try solve [inversion H].
    destruct ((b =? b0)%string && Ty_eqb t1 t && dec_Term t0 t3); try solve [inversion H].
    specialize (IHbs _ _ H).

    destruct IHbs as [fs H_fs].

    exists (
      desugar_fun b0 t t3
      ::
      fs).
    unfold desugar_fun.
    subst t2.
    simpl.
    reflexivity.
Qed.

Lemma dec_funs_exists : ∀ fs t t_inner,
  Forall (fun f => ∃ v ty t_bound, f = desugar_fun v ty t_bound) fs ->
  fold_right apply t_inner fs = t ->
  ∃ bs, dec_Bindings bs t = Some t_inner
.
Proof.
  admit.
Admitted.

Definition dec_Term_equiv : ∀ t, P_Term t.
Proof.
  apply term__multind with (P := P_Term) (Q := P_Binding).
  all: try solve [dec_tac].
  - (* P_Term Let *)
    destruct rec.
    + (* NonRec *)
      admit.
    + (* Rec *)
      unfold P_Term, P_Binding;
      intros;

      (* Split cases, solve impossible ones *)
      match goal with t' : term |- _ =>
        destruct t'; split; try solve [inversion 1]
      end.
      * (*fwd *) 
      intros.
      simpl_dec_Term.
      rewrite ForallP_Forall in *.
      apply (Forall_impl P_Binding_compat (fun b H => proj1 H)) in H.
        unfold P_Binding_compat in *.
      apply (forall2b_Forall2_Forall _ _ dec_Binding_compat _ _ H) in H1.

      apply H0 in H2.
      constructor; auto.
      generalize dependent l.
      induction bs.
      -- intros l H1. inversion H1. constructor.
      -- intros l H1. inversion H1; subst.
         apply Forall_inv_tail in H.
         constructor; eauto.
      (* bwd *)
      * intros H_Let.
        inversion H_Let. subst.
        simpl.
        rewrite andb_true_iff.
        split.
        -- rewrite ForallP_Forall in H.
        apply (Forall_impl P_Binding_compat (fun b H => proj1 H)) in H.
        apply (forall2b_Forall2_Forall _ _ dec_Binding_compat _ _ H).
        generalize dependent l.
        induction bs.
        --- intros l H_Let H_compat.
            inversion H_compat. subst. constructor.
        --- intros l H_Let H_compat. inversion H_compat; subst.
            constructor; auto.
            inversion H_Let; subst.
            inversion H9; subst.
            eapply IHbs; eauto using Forall_inv_tail.
            eauto using CNR_Term.
        -- rewrite H0. assumption.
  - (* P_Binding TermBind *)
  unfold P_Term, P_Binding;
  unfold P_Binding_compat, P_Binding_NonRec.
  intros.
  split.
  + (* compat *)
    split.
    * (* fwd*)
      destruct b'; try solve [inversion 1].
      intros.
      simpl in H0.
      simpl_dec_Term.
      rewrite_reflection.
      subst.
      eauto using CNR_Binding_compat.
    * (* bwd *)
      destruct b'; try solve [inversion 1].
      inversion 1; subst.
      simpl_goal.
      repeat split; bwd_reflection.
  + (* P_Binding_NonRec *)
    intros.
    split.
    * (* ∃ fs *)
      intros.
      destruct H0.
      (* simplify dec_Bindings *)
      destruct s;
        try solve [inversion H0]. (* Impossible case*)
      destruct v.
      simpl in H0.
      repeat (match goal with
        | H : match ?t with _ => _ end = _ |- _ => destruct t
      end); try solve [inversion H0].

      exists (desugar_fun b0 t0 t0_2).
      apply dec_Bindings_exists in H0 as [fs H_fs].
      exists fs.
      split.
      ** admit.
      ** unfold apply, desugar_fun. subst t0_1. simpl. reflexivity.
    * admit.

  - (* P_Binding TypeBind *)
    intros.
    unfold P_Binding, P_Binding_compat, P_Binding_NonRec.
    split; admit.
  - (* P_Binding DatatypeBind *)
    admit.
Admitted.
