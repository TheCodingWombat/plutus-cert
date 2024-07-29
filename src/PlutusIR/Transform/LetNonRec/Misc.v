From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import PlutusIR.Transform.Compat.
From PlutusCert Require Import PlutusIR.Analysis.FreeVars.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Import Coq.Lists.List.ListNotations.

From PlutusCert Require Import LetNonRec.Spec.

(* Functional specification of the pass *)
Fixpoint compile_term (t : term) : term := match t with
  | Let NonRec bs t => fold_right apply t (map compile_NonRec_Binding bs)
  | Let Rec bs t    => Let Rec (map compile_Rec_Binding bs) (compile_term t)

  | TyAbs α k t     => TyAbs α k (compile_term t)
  | LamAbs x τ t    => LamAbs x τ (compile_term t)
  | Apply t1 t2     => Apply (compile_term t1) (compile_term t2)
  | IWrap σ τ t     => IWrap σ τ (compile_term t)
  | Unwrap t        => Unwrap (compile_term t)
  | TyInst t τ      => TyInst (compile_term t) τ

  | Var x           => Var x
  | Constant c      => Constant c
  | Builtin f       => Builtin f
  | Error τ         => Error τ
  | Constr i ts     => Constr i (map compile_term ts)
  | Case t ts       => Case (compile_term t) (map compile_term ts)
  end

with compile_NonRec_Binding (b : binding) : term -> term :=
  match b with
  | TermBind Strict (VarDecl v ty) t_bound => fun t_bs => Apply (LamAbs v ty t_bs) (compile_term t_bound)
  | _ => id
  end

with compile_Rec_Binding (b : binding) : binding := match b with
  | TermBind Strict vd t_bound => TermBind Strict vd (compile_term t_bound)
  | b => b
  end
  .

(* Constructors where equalities in indices are made
   explicit *)
Ltac eq_principle :=
  intros;
  subst;
  constructor;
  assumption.

Definition C_TyAbs' : forall R (t t' : term) (n n' : string) (k k' : kind),
              n = n' -> k = k'
              -> R t t' -> Compat R (TyAbs n k t) (TyAbs n' k' t').
Proof. eq_principle. Qed.

Definition C_LamAbs' : forall R (t t' : term) (n n' : string) (ty ty': ty),
                n = n' -> ty = ty' -> R t t' -> Compat R (LamAbs n ty t) (LamAbs n' ty' t').
Proof. eq_principle. Qed.

Definition C_Var' : forall R (n n' : string), (n = n') -> Compat R (Var n) (Var n').
Proof. eq_principle. Qed.

Definition C_Let' : forall R (bs bs' : list binding) (t t' : term) (r r' : recursivity),
             r = r' ->
             Compat_Bindings R bs bs' ->
             R t t' -> Compat R (Let r bs t) (Let r' bs' t').
Proof. eq_principle. Qed.

Definition C_Apply' : forall R (s s' t t' : term),
               R s s' -> R t t' -> Compat R (Apply s t) (Apply s' t').
Proof. eq_principle. Qed.
Definition C_Constant' : forall R (c c' : constant), c = c' -> Compat R (Constant c) (Constant c').
Proof. eq_principle. Qed.
Definition C_Builtin' : forall R (f f' : DefaultFun), f = f' -> Compat R (Builtin f) (Builtin f').
Proof. eq_principle. Qed.
Definition C_TyInst' : forall R (t t' : term) (ty ty' : ty),
                ty = ty' -> R t t' -> Compat R (TyInst t ty) (TyInst t' ty').
Proof. eq_principle. Qed.

Definition C_Error' : forall R (ty ty' : ty), ty = ty' -> Compat R (Error ty) (Error ty').
Proof. eq_principle. Qed.

Definition C_IWrap' : forall R (t t' : term) (ty1 ty1' ty2 ty2' : ty),
               ty1 = ty1' -> ty2 = ty2' -> R t t' -> Compat R (IWrap ty1 ty2 t) (IWrap ty1' ty2' t').
Proof. eq_principle. Qed.
Definition C_Unwrap' : forall R (t t' : term), R t t' -> Compat R (Unwrap t) (Unwrap t').
Proof. eq_principle. Qed.

Create HintDb eq_principles.
#[global]
Hint Resolve C_Let' C_Var' C_LamAbs' C_TyAbs' C_Apply' C_Constant' C_Builtin' C_TyInst' C_Error' C_IWrap' C_Unwrap : eq_principles.

(*
Definition CNR_Let' : forall (bs : list Binding) (t1 t1' t2 t2' t3 t3' : Term),
  t1 = t1' -> t2 = t2' -> t3 = t3' ->
  CNR_Term t1 t2 ->
  CNR_Bindings bs f_bs -> CNR_Term (Let NonRec bs t1') t3'.
Proof. intros. subst. eapply CNR_Let.
  + apply X.
  + apply X0.
  Qed.
*)

Definition CNR_Desugar'
    : forall v v' t_bound t_bound' ty,
        v = v' ->
        CNR_Term t_bound t_bound' ->
        CNR_Binding
          (TermBind Strict (VarDecl v ty) t_bound)
          (fun t_bs => Apply (LamAbs v' ty t_bs) t_bound').
Proof.
  intros. subst. apply CNR_Desugar. assumption.
Qed.

