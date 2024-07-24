Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Bool.BoolEq.
Require Import Ascii.
Require Import Eqdep.

From PlutusCert Require Import Util.
Set Implicit Arguments.

Require Import Coq.Program.Basics.

Import ListNotations.


From QuickChick Require Import QuickChick.
(*
  Simplification of the names in the AST

  In the AST that we dump in the plutus compiler, variables are represented with the Name type, which is
  a pair of String and Int, where the Int (newtyped as Unique) is used as a compiler detail for cheap name
  comparisons (see Language.PlutusCore.Name.

  We ignore these details and treat names (both terms and types) as strings. The definitions
  below have the same types as the original AST constructors, but forget the structure and
  map to a string.

  This simplifies the representation and especially recognizing equal subterms (since
  compiler passes may reassign unique numbers).

  Possible future approach: it is preferable to have to complete AST including e.g.
  Uniques, but prove that they do not matter for evaluation and then remove them from
  AST

*)

(** recursivity and strictness *)
Inductive recursivity := NonRec | Rec.

Inductive strictness := NonStrict | Strict.

(** Default universe

In the compiler implementation, this is a GADT: the constructors have an index
for their Haskell interpretation. This enforces that only well-kinded types can be constructed.
Since types may have different kinds (e.g. List vs Integer), the GADT is not directly
annotated with its type, but by its (Haskell) kind and its (Haskell) type. The (Haskell) kind
is not visible though, as it is existentially quantified. For example:

    -- Existential quantification of a kind.
    data Esc = forall k. Esc k

    data DefaultUni =
    ...
    | DefaultUniApply ::
       !(DefaultUni (Esc f)) -> !(DefaultUni (Esc a)) -> DefaultUni (Esc (f a))

This approach makes that one can construct plutus types that are of higher kind, e.g.

  Ty_Builtin (SomeTypeIn DefaultUniList)

This is useful for polymorphic function types (see compiler Note [Representing polymorphism]).

For representing constants of builtin types (which can only have kind * ), the compiler has

  data ValueOf uni a = ValueOf !(uni (Esc a)) !a

Since the last argument a is inferred as kind *, the use of GADT for DefaultUniverse will
only construct values of plutus types with the right kind.

In our Coq encoding, we don't use indexed types, as Coq doesn't always have the same
conveniences for pattern matching, and automatisation such as deriving. Instead we can
have dependently typed functions that compute the right types for constructing values
(see uniType and Constant).
*)
Inductive DefaultUni : Type :=
    | DefaultUniInteger
    | DefaultUniByteString
    | DefaultUniString
    | DefaultUniUnit
    | DefaultUniBool
    | DefaultUniProtoList
    | DefaultUniProtoPair
    | DefaultUniData
    | DefaultUniBLS12_381_G1_Element
    | DefaultUniBLS12_381_G2_Element
    | DefaultUniBLS12_381_MlResult

    | DefaultUniApply : DefaultUni -> DefaultUni -> DefaultUni
    .

QCDerive EnumSized for DefaultUni.

(** Existentials as a datype *)
Inductive some {f : DefaultUni -> Type} :=
  Some' : forall {u : DefaultUni}, f u -> some.
Arguments some _ : clear implicits.

(** Builtin types *)
Inductive typeIn (u : DefaultUni) :=
  TypeIn : typeIn u.
Arguments TypeIn _ : clear implicits.

(* This synonym exists since the Haskell plutus implementation cannot reuse
   the Some type. In Coq we can. *)
Definition SomeTypeIn (ty : DefaultUni) := @Some' typeIn ty (TypeIn ty).


Inductive Data :=
  | DataConstr : Z -> list Data -> Data
  | DataMap : list (Data * Data) -> Data
  | DataList : list Data -> Data
  | DataI : Z -> Data
  | DataB : string -> Data
  .

(** Coq interpretation of plutus built-in types of base kind. If not of
* base-kind (or not well-kinded), returns None.
*)
Fixpoint uniType_option (x : DefaultUni) : option Set :=
  match x with
    | DefaultUniInteger    => Some Z
    | DefaultUniByteString => Some string
    | DefaultUniString => Some string
    | DefaultUniUnit => Some unit
    | DefaultUniData => Some Data
    | DefaultUniBLS12_381_G1_Element => Some Z
    | DefaultUniBLS12_381_G2_Element => Some Z
    | DefaultUniBLS12_381_MlResult => Some Z
    | DefaultUniBool => Some bool

    | DefaultUniApply DefaultUniProtoList t =>
      match uniType_option t with
        | None => None
        | Some A => Some (list A)
      end

    | DefaultUniApply (DefaultUniApply DefaultUniProtoPair s) t =>
      match uniType_option s, uniType_option t with
      | Some A, Some B => Some (prod A B)
      | _, _ => None
      end

    | DefaultUniApply _ _ => None
    | DefaultUniProtoList => None
    | DefaultUniProtoPair => None
  end
  .
Functional Scheme uniType_option_rect := Induction for uniType_option Sort Type.


(** Coq interpretation of plutus built-in types of base kind. Used for constructing
constants (See term.Constant). Types that are ill-kinded or do not have base kind are
mapped to the empty type, ensuring that Constants of such type can be constructed.
*)
Definition uniType (x : DefaultUni) : Type :=
  match uniType_option x with
    | None => Empty_set
    | Some ty => ty
  end.

Inductive valueOf (u : DefaultUni) :=
  ValueOf : uniType u -> valueOf u.
Arguments ValueOf _ _ : clear implicits.

(** Built-in functions*)
Inductive DefaultFun :=

    | AddInteger
    | SubtractInteger
    | MultiplyInteger
    | DivideInteger
    | QuotientInteger
    | RemainderInteger
    | ModInteger
    | EqualsInteger
    | LessThanInteger
    | LessThanEqualsInteger
    (* Bytestrings *)
    | AppendByteString
    | ConsByteString
    | SliceByteString
    | LengthOfByteString
    | IndexByteString
    | EqualsByteString
    | LessThanByteString
    | LessThanEqualsByteString
    (* Cryptography and hashes *)
    | Sha2_256
    | Sha3_256
    | Blake2b_256
    | VerifyEd25519Signature  (* formerly verifySignature *)
    | VerifyEcdsaSecp256k1Signature
    | VerifySchnorrSecp256k1Signature
    (* Strings *)
    | AppendString
    | EqualsString
    | EncodeUtf8
    | DecodeUtf8
    (* Bool *)
    | IfThenElse
    (* Unit *)
    | ChooseUnit
    (* Tracing *)
    | Trace
    (* Pairs *)
    | FstPair
    | SndPair
    (* Lists *)
    | ChooseList
    | MkCons
    | HeadList
    | TailList
    | NullList
    (* Data *)
    | ChooseData
    | ConstrData
    | MapData
    | ListData
    | IData
    | BData
    | UnConstrData
    | UnMapData
    | UnListData
    | UnIData
    | UnBData
    | EqualsData
    | SerialiseData
    (* Misc monomorphized constructors. *)
    | MkPairData
    | MkNilData
    | MkNilPairData
    (* BLS12_381 operations *)
    (* G1 *)
    | Bls12_381_G1_add
    | Bls12_381_G1_neg
    | Bls12_381_G1_scalarMul
    | Bls12_381_G1_equal
    | Bls12_381_G1_hashToGroup
    | Bls12_381_G1_compress
    | Bls12_381_G1_uncompress
    (* G2 *)
    | Bls12_381_G2_add
    | Bls12_381_G2_neg
    | Bls12_381_G2_scalarMul
    | Bls12_381_G2_equal
    | Bls12_381_G2_hashToGroup
    | Bls12_381_G2_compress
    | Bls12_381_G2_uncompress
    (* Pairing *)
    | Bls12_381_millerLoop
    | Bls12_381_mulMlResult
    | Bls12_381_finalVerify
    (* Keccak_256, Blake2b_224 *)
    | Keccak_256
    | Blake2b_224
.

Definition name := string.
Definition tyname := string.
Definition binderName := string.
Definition binderTyname := string.

(** kinds *)
Inductive kind :=
  | Kind_Base : kind
  | Kind_Arrow : kind -> kind -> kind.

(** Types *)
Inductive ty :=
  | Ty_Var : tyname -> ty
  | Ty_Fun : ty -> ty -> ty
  | Ty_IFix : ty -> ty -> ty
  | Ty_Forall : binderTyname -> kind -> ty -> ty
  | Ty_Builtin : @some typeIn -> ty
  | Ty_Lam : binderTyname -> kind -> ty -> ty
  | Ty_App : ty -> ty -> ty
  (* | Ty_SOP : list (list ty) -> ty *)
.
(*
  Note [Simplification of AST representation]

  In the Haskell AST, term is a functor and each constructor may have a field of
  the type parameter `a`. This seems to be used for internal metadata on the
  AST. At the moment we don't use it and don't represent it in the AST.

*)

(** Declarations *)
Inductive vdecl := VarDecl : binderName -> ty -> vdecl.
Inductive tvdecl := TyVarDecl : binderTyname -> kind -> tvdecl.
Inductive dtdecl := Datatype : tvdecl -> list tvdecl -> binderName -> list vdecl -> dtdecl.

(** terms and bindings *)
(* Perhaps parametrize to mimic original AST in haskell more closely? We really only need one instantiation for now. *)
(* Context {func : Type} {uni : Type -> Type} {name : Type} {tyname : Type}. *)
Inductive term :=
  | Let      : recursivity -> list binding -> term -> term
  | Var      : name -> term
  | TyAbs    : binderTyname -> kind -> term -> term
  | LamAbs   : binderName -> ty -> term -> term
  | Apply    : term -> term -> term
  | Constant : @some valueOf -> term
  | Builtin  : DefaultFun -> term
  | TyInst   : term -> ty -> term
  | Error    : ty -> term
  | IWrap    : ty -> ty -> term -> term
  | Unwrap   : term -> term
  | Constr   : nat -> list term -> term
  | Case     : term -> list term -> term

with binding :=
  | TermBind : strictness -> vdecl -> term -> binding
  | TypeBind : tvdecl -> ty -> binding
  | DatatypeBind : dtdecl -> binding
.


(* AST Annotations *)
Inductive datatype_component :=
  | Constructor
  | ConstructorType
  | Destructor
  | DestructorType
  | DatatypeType
  | PatternFunctor
.

Inductive provenance a :=
  | Original          : a -> provenance a
  | LetBinding        : recursivity -> provenance a -> provenance a
  | TermBinding       : list ascii -> provenance a -> provenance a
  | TypeBinding       : list ascii -> provenance a -> provenance a
  | DatatypeComponent : datatype_component -> provenance a -> provenance a
  | MultipleSources   : list (provenance a) -> provenance a
.

Inductive inline_annot :=
  | AlwaysInline
  | MayInline
.

Inductive src_span :=
  | SrcSpan : list ascii -> nat -> nat -> nat -> nat -> src_span
.

Inductive ann :=
  | Ann : inline_annot -> list src_span -> ann
.

Inductive context :=
  | C_Hole     : context

  | C_LamAbs   : binderName -> ty -> context -> context
  | C_Apply_L    : context -> term -> context
  | C_Apply_R    : term -> context -> context
  .

(* Similar to mkLet in Plutus: for an empty list of bindings it is the identity, otherwise
   it constructs a let with a non-empty list of bindings *)
Definition mk_let (r : recursivity) (bs : list binding) (t : term) : term :=
  match bs with
    | [] => t
    | _  => Let r bs t
  end
.

Fixpoint context_apply (C : context) (t : term) :=
  match C with
    | C_Hole           => t
    | C_LamAbs bn ty C => LamAbs bn ty (context_apply C t)
    | C_Apply_L C t'   => Apply (context_apply C t) t'
    | C_Apply_R t' C   => Apply t' (context_apply C t)
  end
.

(** ** Trace of compilation *)
Inductive pass :=
  | PassRename
  | PassTypeCheck
  | PassInline : list name -> pass
  | PassDeadCode
  | PassThunkRec
  | PassFloatTerm
  | PassLetNonStrict
  | PassLetTypes
  | PassLetRec
  | PassLetNonRec.

Inductive compilation_trace :=
  | CompilationTrace : term -> list (pass * term) -> compilation_trace.


(* AST Helpers *)

Definition vdecl_name : vdecl -> binderName :=
  fun c => match c with
  | VarDecl n _ => n
  end
  .

Definition vdecl_ty : vdecl -> ty :=
  fun c => match c with
  | VarDecl _ ty => ty
  end
  .

Definition tvdecl_name (tvd : tvdecl) : binderTyname :=
  match tvd with
  | TyVarDecl v K => v
  end.

Section term__ind.

  Unset Implicit Arguments.

  Variable (P : term -> Prop).
  Variable (Q : binding -> Prop).

  Context
    (H_Let     : forall rec bs t, ForallP Q bs -> P t -> P (Let rec bs t))
    (H_Var     : forall s : string, P (Var s))
    (H_TyAbs   : forall (s : string) (k : kind) (t : term), P t -> P (TyAbs s k t))
    (H_LamAbs  : forall (s : string) (t : ty) (t0 : term), P t0 -> P (LamAbs s t t0))
    (H_Apply   : forall t : term, P t -> forall t0 : term, P t0 -> P (Apply t t0))
    (H_Constant : forall s : some valueOf, P (Constant s))
    (H_Builtin : forall d : DefaultFun, P (Builtin d))
    (H_TyInst  : forall t : term, P t -> forall t0 : ty, P (TyInst t t0))
    (H_Error   : forall t : ty, P (Error t))
    (H_IWrap   : forall (t t0 : ty) (t1 : term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap  : forall t : term, P t -> P (Unwrap t))
    (H_Constr  : forall (i : nat) (ts : list term), ForallP P ts -> P (Constr i ts))
    (H_Case   : forall (t : term), P t -> forall ts, ForallP P ts -> P (Case t ts))
    .



  Context
    (H_TermBind : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Definition bindings__ind (binding__ind : forall (b : binding), Q b) :=
    fix bindings__ind bs :=
    match bs as p return ForallP Q p with
      | nil       => ForallP_nil
      | cons b bs => ForallP_cons (binding__ind b) (bindings__ind bs)
    end.

  Definition terms__ind (term_rect : forall (t : term), P t) :=
    fix terms_rect' ts :=
    match ts as p return ForallP P p with
      | nil       => ForallP_nil
      | cons t ts => ForallP_cons (term_rect t) (terms_rect' ts)
    end.

  Fixpoint term__ind (t : term) : P t :=
    match t with
      | Let rec bs t    => H_Let rec bs t (bindings__ind binding__ind bs) (term__ind t)
      | Var n           => H_Var n
      | TyAbs n k t     => H_TyAbs n k t (term__ind t)
      | LamAbs n ty t   => H_LamAbs n ty t (term__ind t)
      | Apply s t       => H_Apply s (term__ind s) t (term__ind t)
      | TyInst t ty     => H_TyInst t (term__ind t) ty
      | IWrap ty1 ty2 t => H_IWrap ty1 ty2 t (term__ind t)
      | Unwrap t        => H_Unwrap t (term__ind t)
      | Error ty        => H_Error ty
      | Constant v      => H_Constant v
      | Builtin f       => H_Builtin f
      | Constr i ts     => H_Constr i ts (terms__ind term__ind ts)
      | Case t ts      => H_Case t (term__ind t) ts (terms__ind term__ind ts)
    end
  with binding__ind (b : binding) : Q b :=
    match b with
      | TermBind s v t  => H_TermBind s v t (term__ind t)
      | TypeBind v ty   => H_TypeBind v ty
      | DatatypeBind dtd => H_DatatypeBind dtd
    end.

  Combined Scheme term__multind from term__ind, binding__ind.

End term__ind.

Section term_rect.
  Variable (P : term -> Type).
  Variable (Q : binding -> Type).
  Variable (R : list binding -> Type).

  Context
    (* (H_Let     : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t)) *)
    (H_Let     : forall rec bs t, R bs -> P t -> P (Let rec bs t))
    (H_Var     : forall s, P (Var s))
    (H_TyAbs   : forall s (k : kind) (t : term), P t -> P (TyAbs s k t))
    (H_LamAbs  : forall s t (t0 : term), P t0 -> P (LamAbs s t t0))
    (H_Apply   : forall t : term, P t -> forall t0 : term, P t0 -> P (Apply t t0))
    (H_Constant : forall s : some valueOf, P (Constant s))
    (H_Builtin : forall d : DefaultFun, P (Builtin d))
    (H_TyInst  : forall t : term, P t -> forall t0 : ty, P (TyInst t t0))
    (H_Error   : forall t : ty, P (Error t))
    (H_IWrap   : forall (t t0 : ty) (t1 : term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap  : forall t : term, P t -> P (Unwrap t))
    (H_Constr  : forall (i : nat) (ts : list (term)), ForallT P ts -> P (Constr i ts))
    (H_Case   : forall t, P t -> forall ts, ForallT P ts -> P (Case t ts)).

  Context
    (H_TermBind    : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind    : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Context
    (H_cons        : forall b bs, Q b -> R bs -> R (b :: bs))
    (H_nil         : R nil).

  Definition bindings_rect' (binding_rect' : forall (b : binding), Q b) :=
    fix bindings_rect' bs :=
    match bs return R bs with
      | nil       => @H_nil
      | cons b bs => @H_cons _ bs (binding_rect' b) (bindings_rect' bs)
    end.

  Definition terms_rect' (term_rect : forall (t : term), P t) :=
    fix terms_rect' ts :=
    match ts as p return ForallT P p with
      | nil       => ForallT_nil
      | cons t ts => ForallT_cons (term_rect t) (terms_rect' ts)
    end.

  Fixpoint term_rect' (t : term) : P t :=
    match t with
      | Let rec bs t    => @H_Let rec bs t (bindings_rect' binding_rect' bs) (term_rect' t)
      | Var n           => @H_Var n
      | TyAbs n k t     => @H_TyAbs n k t (term_rect' t)
      | LamAbs n ty t   => @H_LamAbs n ty t (term_rect' t)
      | Apply s t       => @H_Apply s (term_rect' s) t (term_rect' t)
      | TyInst t ty     => @H_TyInst t (term_rect' t) ty
      | IWrap ty1 ty2 t => @H_IWrap ty1 ty2 t (term_rect' t)
      | Unwrap t        => @H_Unwrap t (term_rect' t)
      | Error ty        => @H_Error ty
      | Constant v      => @H_Constant v
      | Builtin f       => @H_Builtin f
      | Constr i ts     => @H_Constr i ts (terms_rect' term_rect' ts)
      | Case t ts      => @H_Case t (term_rect' t) ts (terms_rect' term_rect' ts)
    end
  with binding_rect' (b : binding) : Q b :=
    match b with
      | TermBind s v t   => @H_TermBind s v t (term_rect' t)
      | TypeBind v ty    => @H_TypeBind v ty
      | DatatypeBind dtd => @H_DatatypeBind dtd
    end.
End term_rect.

Section ty_fold.

  Context
    {R : Set}.

  Context
    (f_Var : name -> R)
    (f_Fun : R -> R -> R)
    (f_IFix : R -> R -> R)
    (f_Forall :  binderName -> kind -> R -> R)
    (f_Builtin : @some typeIn -> R)
    (f_Lam :  binderName -> kind -> R -> R)
    (f_App : R -> R -> R)
    (f_SOP_prod_cons : R -> R -> R)
    (f_SOP_prod_nil : R)
    (f_SOP_sum_cons : R -> R -> R)
    (f_SOP_sum_nil : R)
    .

  Definition ty_fold := fix fold ty :=
    match ty with
    | Ty_Var v        => f_Var v
    | Ty_Fun t1 t2    => f_Fun (fold t1) (fold t2)
    | Ty_IFix t1 t2   => f_IFix (fold t1) (fold t2)
    | Ty_Forall v k t => f_Forall v k (fold t)
    | Ty_Builtin b    => f_Builtin b
    | Ty_Lam v k t    => f_Lam v k (fold t)
    | Ty_App t1 t2    => f_App (fold t1) (fold t2)
    (*
    | Ty_SOP xs => 
      ((fix f xs := match xs with
        | ys :: xs' =>
          f_SOP_sum_cons
            ((fix g ys :=
              match ys with
              | ty :: ys' => f_SOP_prod_cons (fold ty) (g ys')
              | [] => f_SOP_prod_nil
              end
            ) ys)
            (f xs')
        | [] => f_SOP_sum_nil
      end
      ) xs) *)
    end
.

  Definition ty_alg (ty : ty) : Set := match ty with
    | Ty_Var v        => name -> R
    | Ty_Fun t1 t2    => R -> R -> R
    | Ty_IFix t1 t2   => R -> R -> R
    | Ty_Forall v k t =>  binderName -> kind -> R -> R
    | Ty_Builtin b    => @some typeIn -> R
    | Ty_Lam v k t    =>  binderName -> kind -> R -> R
    | Ty_App t1 t2    => R -> R -> R
    (* | Ty_SOP tys      => (R -> R -> R * R * R -> R -> R * R) *)
    end.

End ty_fold.


Definition ty_endo (m_custom : forall τ, option (@ty_alg ty τ)) := fix f τ :=
  match m_custom τ with
    | Some f_custom => match τ return ty_alg τ -> ty with
      | Ty_Var v        => fun f_custom => f_custom v
      | Ty_Fun t1 t2    => fun f_custom => f_custom (f t1) (f t2)
      | Ty_IFix t1 t2   => fun f_custom => f_custom (f t1) (f t2)
      | Ty_Forall v k t => fun f_custom => f_custom v k (f t)
      | Ty_Builtin b    => fun f_custom => f_custom b
      | Ty_Lam v k t    => fun f_custom => f_custom v k (f t)
      | Ty_App t1 t2    => fun f_custom => f_custom (f t1) (f t2)
    end f_custom
    | None =>
      match τ with
      | Ty_Var v        => Ty_Var v
      | Ty_Fun t1 t2    => Ty_Fun (f t1) (f t2)
      | Ty_IFix t1 t2   => Ty_IFix (f t1) (f t2)
      | Ty_Forall v k t => Ty_Forall v k (f t)
      | Ty_Builtin b    => Ty_Builtin b
      | Ty_Lam v k t    => Ty_Lam v k (f t)
      | Ty_App t1 t2    => Ty_App (f t1) (f t2)
      end
  end.

Definition unitVal : term := Constant (Some' (ValueOf DefaultUniUnit tt)).



Declare Scope plutus_scope.

Declare Custom Entry plutus_term.
Declare Custom Entry plutus_ty.
Declare Custom Entry plutus_kind.

Module PlutusNotations.

  Notation "<{ e }>" := e (e custom plutus_term at level 99) : plutus_scope.
  Notation "<{{ e }}>" := e (e custom plutus_ty at level 99) : plutus_scope.
  Notation "<{{{ e }}}>" := e (e custom plutus_kind at level 99) : plutus_scope.
  Notation "( x )" := x (in custom plutus_term, x at level 99) : plutus_scope.
  Notation "( x )" := x (in custom plutus_ty, x at level 99) : plutus_scope.
  Notation "( x )" := x (in custom plutus_kind, x at level 99) : plutus_scope.
  Notation "x" := x (in custom plutus_term at level 0, x constr at level 0) : plutus_scope.
  Notation "x" := x (in custom plutus_ty at level 0, x constr at level 0) : plutus_scope.
  Notation "x" := x (in custom plutus_kind at level 0, x constr at level 0) : plutus_scope.
  Notation "{ x }" := x (in custom plutus_term at level 1, x constr) : plutus_scope.
  Notation "{ x }" := x (in custom plutus_ty at level 1, x constr) : plutus_scope.
  Notation "{ x }" := x (in custom plutus_kind at level 1, x constr) : plutus_scope.

  #[global]
  Open Scope plutus_scope.
End PlutusNotations.
