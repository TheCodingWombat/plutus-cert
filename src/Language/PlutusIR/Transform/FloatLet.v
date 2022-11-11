Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
From PlutusCert Require Import
  Language.PlutusIR
  Transform.Congruence
  Analysis.Equality
  Analysis.FreeVars
  Analysis.UniqueBinders
  Analysis.Purity
  Static.Typing.
Import NamedTerm.


Notation fv := (free_vars String.eqb).

(* Find adjacent lets of given recursivity at the top of the AST *)
Fixpoint adjacentBindings r (t : Term) : list Binding * Term :=
    match t with
      | Let r' bs t => if Recursivity_eqb r' r
          then
            let (bs', t') := adjacentBindings r t
            in (bs ++ bs', t')
          else (nil, t)
      | _            => (nil, t)
    end.


(* Adjacent let-binding groups (with same recursivity) can be merged *)
Inductive LetMerge : Term -> Term -> Prop :=
  | LM_Merge : forall bs bs' bs'' r t t' t'',
                   (bs', t') = adjacentBindings r t
                -> ZipWith (BindingBy LetMerge) (bs ++ bs') bs''
                -> LetMerge t' t''
                -> LetMerge (Let r bs   t )
                            (Let r bs'' t'')

  (* Todo: if we want to generalize it so that not all adjacent let-groups are merged (more
     general), we probably need some relation instead of the function adjacentBindings
  *)
  | LM_Cong : forall t t', Cong LetMerge t t' -> LetMerge t t'.



Section SubList.

  Inductive SubList {a} : list a -> list a -> Type :=
    | SL_nil  : forall ys     ,                             SubList nil       ys
    | SL_cons : forall x xs ys, In x ys -> SubList xs ys -> SubList (x :: xs) ys
    .

End SubList.



(* Apply a single swap in a list, given that the elements are related
   through R *)
Inductive SwapIn {a : Type} {R : a -> a -> Type} : list a -> list a -> Type :=

  | Swap_Top : forall {x1 x2 xs},
      R x1 x2 ->
      SwapIn (x1 :: x2 :: xs) (x2 :: x1 :: xs)

  | Swap_Pop  : forall {x xs xs'},
      SwapIn       xs        xs' ->
      SwapIn (x :: xs) (x :: xs')
  .
Arguments SwapIn {_} _.

(* Apply multiple swaps in a a list (transitive closure) *)
Inductive SwapsIn {a : Type} (R : a -> a -> Type) : list a -> list a -> Type :=
  | SwapsIn_cons : forall xs ys zs,
      SwapIn R xs ys ->
      SwapsIn R ys zs ->
      SwapsIn R xs zs
  | SwapsIn_nil  : forall xs, SwapsIn R xs xs.



(*
 Can non-recursive bindings
    { x = xt; y = yt }
 be rewritten to
    { y = yt; x = xt}
 ?
*)
Inductive Bindings_NonRec_Commute : Binding -> Binding -> Type :=
  | BC_NonStrict:  forall x y xt yt T,
       ~ (x = y)         -> (* They can't bind the same name.
                               Although this could be allowed in specific cases,
                               when both are dead bindings, or are binding
                               equivalent terms *)
       ~ (In x (fv yt)) -> (* yt may not depend on x *)
       ~ (In y (fv xt)) -> (* if xt has a free var y, swapping would shadow that variable *)

       Bindings_NonRec_Commute
         (TermBind NonStrict (VarDecl x T) xt)
         (TermBind NonStrict (VarDecl y T) yt)

  | BC_DatatypeL: forall ty args matchf constructors strictness x xt T,
       Forall (fun v => ~(In v (fv xt))) (matchf :: (map constructorName constructors)) ->
       Bindings_NonRec_Commute
         (DatatypeBind (Datatype ty args matchf constructors))
         (TermBind strictness (VarDecl x T) xt)

  (* e.g. BC_DatatypeR := BC_Symm (BC_DatatypeL) *)
  | BC_Symm : forall x y,
       Bindings_NonRec_Commute x y ->
       Bindings_NonRec_Commute y x

  | BC_Datatypes: forall ty ty' args args' matchf matchf' cs cs',
       Bindings_NonRec_Commute
         (DatatypeBind (Datatype ty args matchf cs))
         (DatatypeBind (Datatype ty' args' matchf' cs'))
  .

(* Given two non-recursive term-binding groups bs and cs, where cs is a reordering of bs

    - if cs = (c :: _), c must have a related binding b in bs, that is:

        bs = bs_pre ++ [b] ++ bs_post

      since b was moved to the top of the binding group, that is only correct when:
        + b does not depend on any binding in bs_pre
        + b does not shadow any binding in bs_pre (moving it to the top
      (it commutes with all bindings in bs_pre)

    - if cs = [] then bs = nil
*)

(* Two non-recursive bindings may be reordered if:
   - the latter does not depend on the former
   - the latter does not bind (shadow) a free variable in the former
   - neither are a "let-effectful" (i.e. they strictly bind a non-value expression, which may have
     side effects such as error)
*)


(* Reorder bindings within a non-recursive binding group*)
Inductive LetReorder : Term -> Term -> Type :=
  | LR_Let  : forall t t' bs bs' bs'', LetReorder t t' ->
                 ZipWith (BindingBy LetReorder) bs bs' ->
                 SwapsIn Bindings_NonRec_Commute bs' bs'' ->
                 LetReorder
                   (Let NonRec bs   t )
                   (Let NonRec bs'' t')

  | LR_Cong : forall t t', Cong LetReorder t t' -> LetReorder t t'.
(*
with LetReorder_Binding : Binding -> Binding -> Type :=
  | LR_TermBind  : forall t t' s v,
     LetReorder t t' -> LetReorder_Binding (TermBind s v t) (TermBind s v t')
  | LR_OtherBind : forall b,
     LetReorder_Binding b b.
     *)


(* This definition assumes global uniqueness *)
Inductive let_reorder : Term -> Term -> Prop :=

  | lr_Let : forall r bs bs' t t',
      let_reorder_Bindings bs bs' ->
      let_reorder t t' ->
      let_reorder (Let r bs t) (Let r bs' t')

  | lr_cong : forall t t',
      ~(exists r bs tb, t = Let r bs tb) ->
      Cong let_reorder t t' ->
      let_reorder t t'

with let_reorder_Bindings : list Binding -> list Binding -> Prop :=

  (* Relate pre- and post-bindings one-to-one,
     i.e. there exists a bijection between the pre and post bindings *)
  | lr_cons : forall b bs bs' bs'',
      let_reorder_Binding b bs' bs'' ->
      let_reorder_Bindings bs bs'' ->
      let_reorder_Bindings (b :: bs) bs'

  | lr_nil :
      let_reorder_Bindings [] []


(* Finds a related binding in the list, and returns the other bindings of that list *)
with let_reorder_Binding : Binding -> list Binding -> list Binding -> Prop :=

  | lr_There : forall b b' bs bs',
      let_reorder_Binding b        bs  bs' ->
      let_reorder_Binding b (b' :: bs) (b' :: bs')

  | lr_Here : forall b b' bs,
      Cong_Binding let_reorder b b' ->
      let_reorder_Binding b (b' :: bs) bs
  .


Inductive let_float_step : Term -> Term -> Prop :=

  (* Binding constructs *)
  | lfs_LamAbs : forall x τ r bs t,
      (* TODO: can improve pure_binding with an actual Γ, but the compiler
         doesn't do this either (see `hasNoEffects`) *)
      (* Note, we don't inductively go in to the bindings,
         this is fine, because we eventually transitively close the relation and
         it is possible via lfs_Cong *)
      Forall (pure_binding []) bs ->
      let_float_step (LamAbs x τ (Let r bs t)) (Let r bs (LamAbs x τ t))

  | lfs_TyAbs : forall α k r bs t,
      (* TODO: can improve pure_binding with an actual Γ, but the compiler
         doesn't do this either (see `hasNoEffects`) *)
      Forall (pure_binding []) bs ->
      let_float_step (TyAbs α k (Let r bs t)) (Let r bs (TyAbs α k t))

  | lfs_Let_Binding : forall r1 r2 bs1 bs1' bs2 t,
      let_float_step_Binding bs1 r2 bs2 bs1' ->
      let_float_step (Let r1 bs1 t) (Let r2 bs2 (Let r1 bs1' t))

  | lfs_Let_body : forall r1 r2 bs1 bs1' bs2 bs2' t t',
      let_float_step (Let r1 bs1 (Let r2 bs2 t)) (Let r2 bs2' (Let r1 bs1' t'))

  (* Other constructs *)
  | lfs_Apply_1 : forall s t r bs,
      let_float_step (Apply (Let r bs s) t) (Let r bs (Apply s t))

  | lfs_Apply_2 : forall s t r bs ,
      let_float_step (Apply s (Let r bs t)) (Let r bs (Apply s t))

  | lfs_TyInst : forall r bs t τ,
      let_float_step (TyInst (Let r bs t) τ) (Let r bs (TyInst t τ))

  | lfs_IWrap : forall σ τ r bs t,
      let_float_step (IWrap σ τ (Let r bs t)) (Let r bs (IWrap σ τ t))

  | lfs_Unwrap : forall r bs t ,
      let_float_step (Unwrap (Let r bs t)) (Let r bs (Unwrap t))

  (* Congruence *)

  | lfs_Cong : forall t t',
      Cong let_float_step t t' ->
      let_float_step t t'

with let_float_step_Binding : list Binding -> Recursivity -> list Binding -> list Binding -> Prop :=

  | lfs_Here : forall s vd bs r bs_rhs t,
      (s = NonStrict -> Forall (pure_binding []) bs_rhs) ->
      let_float_step_Binding (TermBind s vd (Let r bs_rhs t) :: bs) r bs_rhs (TermBind s vd t :: bs)

  | lfs_There : forall b bs r bs_rhs,
      let_float_step_Binding bs r bs_rhs bs ->
      let_float_step_Binding (b :: bs) r bs_rhs (b :: bs)
.

Inductive transitive_closure (R : Term -> Term -> Prop) : Term -> Term -> Prop :=
  | tc_id : forall t t',
      R t t' ->
      transitive_closure R t t'

  | tc_trans : forall t t' t'',
      R t t' ->
      R t' t'' ->
      transitive_closure R t t''
.


Definition let_float t_pre t_post
  := Term.unique t_pre
  /\ well_typed t_post
  /\ exists t' t'',
    (  transitive_closure let_float_step t_pre t'
    /\ let_reorder t' t''
    /\ LetMerge t'' t_post
    )
  .
