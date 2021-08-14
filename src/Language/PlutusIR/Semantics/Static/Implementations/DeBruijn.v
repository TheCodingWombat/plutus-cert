Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.
Import DeBruijnTerm.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.


(** ** Contexts and lookups *)
Definition Context := list (Ty + Kind).

Definition empty : Context := nil.

Definition lookupT (ctx : Context) (x : name) : option Ty :=
  match nth_error ctx x with
  | Coq.Init.Datatypes.Some (inl T) => Coq.Init.Datatypes.Some T
  | _ => None
  end.

Definition lookupK (ctx : Context) (X : tyname) : option Kind := 
  match nth_error ctx X with
  | Coq.Init.Datatypes.Some (inr K) => Coq.Init.Datatypes.Some K
  | _ => None
  end.

Definition extendT (x : unit) T ctx : Context := cons (inl T) ctx.
Definition extendK (X : unit) K ctx : Context := cons (inr K) ctx.

Notation "x ':T:' y" := (extendT tt x y) (at level 60, right associativity).
Notation "x ':K:' y" := (extendK tt x y) (at level 60, right associativity).


Definition flatten ctxs : Context := List.concat (rev ctxs).
Definition append ctx1 ctx2 : Context := app ctx1 ctx2.

(*
Definition constructorDecl : constructor -> VDecl :=
  fun c => match c with
  | Constructor vd _ => vd
  end.

(** *** Auxiliary functions *)
Definition getName (vd : VDecl) :=
  match vd with
  | VarDecl x _ => x
  end.

Definition getTy (vd : VDecl) :=
  match vd with
  | VarDecl _ T => T
  end.

Definition getTyname (tvd : TVDecl) :=
  match tvd with
  | TyVarDecl X _ => X
  end.

Definition getKind (tvd : TVDecl) :=
  match tvd with
  | TyVarDecl _ K => K
  end.

Definition getMatchFunc (d : DTDecl) :=
  match d with
  | Datatype _ _ matchFunc _ => matchFunc
  end.

Definition branchTy (c : constructor) (R : Ty) : Ty :=
  match c with
  | Constructor (VarDecl x T) _ => 
    match T with
    | Ty_Fun T1 T2 => Ty_Fun T1 R
    | _ => R
    end
  end.

Open Scope string_scope.

Definition dataTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    let branchTypes : list Ty := map (fun c => branchTy c (Ty_Var "R")) cs in
    let branchTypesFolded := fold_right (@Ty_Fun tyname binderTyname) (Ty_Var "R") branchTypes in
    let indexKinds := map (fun YK => Ty_Lam (getTyname YK) (getKind YK)) YKs in
    fold_right apply (Ty_Forall "R" Kind_Base branchTypesFolded) indexKinds
  end.

Definition dataKind (d : DTDecl) : Kind :=
  match d with
  | Datatype X YKs matchFunc cs =>
    fold_right Kind_Arrow Kind_Base (map getKind YKs)
  end.

Definition constrTy (d : DTDecl) (c : constructor) : Ty :=
  match d, c with
  | Datatype X YKs matchFunc cs, Constructor (VarDecl x T) _ =>
    let indexTyVars := map (compose (@Ty_Var tyname binderTyname) getTyname) YKs in
    let indexTyVarsAppliedToX := fold_left (@Ty_App tyname binderTyname) indexTyVars (Ty_Var (getTyname X)) in
    let branchType := branchTy c indexTyVarsAppliedToX in
    let indexForalls := map (fun YK => Ty_Forall (getTyname YK) (getKind YK)) YKs in
    fold_right apply branchType indexForalls
  end.

Definition matchTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    let indexTyVars := map (compose (@Ty_Var tyname binderTyname) getTyname) YKs in
    let indexTyVarsAppliedToX := fold_left (@Ty_App tyname binderTyname) indexTyVars (Ty_Var (getTyname X)) in
    let indexForalls := map (fun YK => Ty_Forall (getTyname YK) (getKind YK)) YKs in
    fold_right apply (Ty_Fun indexTyVarsAppliedToX (fold_left (@Ty_App tyname binderTyname) indexTyVars (dataTy d))) indexForalls 
  end.

(** *** Binder functions *)
Definition dataBind (d : DTDecl) : tyname * Kind :=
  match d with
  | Datatype X YKs matchFunc cs =>
    (getTyname X, dataKind d)
  end.

Definition constrBind (d : DTDecl) (c : constructor) : name * Ty :=
  match d, c with
  | Datatype X YKs matchFunc cs, Constructor (VarDecl x T) _ =>
    (x, constrTy d c)
  end.

Definition constrBinds (d : DTDecl) : list (name * Ty) :=
  match d with
  | Datatype X YKs matchFunc cs =>
    map (constrBind d) cs
  end.

Definition matchBind (d : DTDecl) : name * Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    (matchFunc, matchTy d)
  end.

Import ListNotations.
Open Scope list_scope.

Definition binds (b : Binding) : Context :=
  match b with
  | TermBind _ vd _ => (getName vd, getTy vd) :T: nil
  | TypeBind tvd ty => (getTyname tvd, getKind tvd) :K: nil
  | DatatypeBind d =>
    let dataB := dataBind d in 
    let constrBs := constrBinds d in
    let constrBs_ctx := fold_right (compose cons inl) nil constrBs in
    let matchB := matchBind d in
    matchB :T: constrBs_ctx ++ (dataB :K: nil)
  end.
*)

Definition binds (b : Binding) : Context := nil.

  (** ** Types of builtin-functions *)
Definition lookupBuiltinTy (f : DefaultFun) : Ty :=
  let Ty_Int := Ty_Builtin (Some (TypeIn DefaultUniInteger)) in
  let Ty_Bool := Ty_Builtin (Some (TypeIn DefaultUniBool)) in
  let Ty_BS := Ty_Builtin (Some (TypeIn DefaultUniByteString)) in
  let T_Int_Bin := Ty_Fun Ty_Int (Ty_Fun Ty_Int Ty_Int) in
  let T_Int_BinPredicate := Ty_Fun Ty_Int (Ty_Fun Ty_Int Ty_Bool) in
  let T_BS_Bin := Ty_Fun Ty_BS (Ty_Fun Ty_BS Ty_BS) in
  let T_BS_BinPredicate := Ty_Fun Ty_BS (Ty_Fun Ty_BS Ty_Bool) in
  let Ty_Char := Ty_Builtin (Some (TypeIn DefaultUniChar)) in
  let Ty_String := Ty_Builtin (Some (TypeIn DefaultUniString)) in
  let Ty_Unit := Ty_Builtin (Some (TypeIn DefaultUniUnit)) in
  match f with
  | AddInteger => T_Int_Bin
  | SubtractInteger => T_Int_Bin
  | MultiplyInteger => T_Int_Bin
  | DivideInteger => T_Int_Bin
  | QuotientInteger => T_Int_Bin
  | RemainderInteger => T_Int_Bin
  | ModInteger => T_Int_Bin
  | LessThanInteger => T_Int_BinPredicate
  | LessThanEqInteger => T_Int_BinPredicate
  | GreaterThanInteger => T_Int_BinPredicate
  | GreaterThanEqInteger => T_Int_BinPredicate
  | EqInteger => T_Int_BinPredicate
  | Concatenate => T_BS_Bin
  | TakeByteString => Ty_Fun Ty_Int (Ty_Fun Ty_BS Ty_BS)
  | DropByteString => Ty_Fun Ty_Int (Ty_Fun Ty_BS Ty_BS)
  | SHA2 => Ty_Fun Ty_BS Ty_BS
  | SHA3 => Ty_Fun Ty_BS Ty_BS
  | VerifySignature => Ty_Fun Ty_BS (Ty_Fun Ty_BS (Ty_Fun Ty_BS Ty_Bool))
  | EqByteString => T_BS_BinPredicate
  | LtByteString => T_BS_BinPredicate
  | GtByteString => T_BS_BinPredicate
  | IfThenElse => Ty_Forall tt Kind_Base (Ty_Fun Ty_Bool (Ty_Fun (Ty_Var 0) (Ty_Fun (Ty_Var 0) (Ty_Var 0))))
  | CharToString => Ty_Fun Ty_Char Ty_String
  | Append => Ty_Fun Ty_String (Ty_Fun Ty_String Ty_String)
  | Trace => Ty_Fun Ty_String Ty_Unit (* TODO: figure out if it is the correct type*)
  end.

(** ** Well-formedness of constructors and bindings *)
Fixpoint listOfArgumentTypes (T : Ty) : list Ty :=
  match T with
  | Ty_Fun T1 T2 => cons T1 (listOfArgumentTypes T2)
  | _ => nil
  end.

(** ** Substitution in types *)
Fixpoint substituteT (X : tyname) (S T : Ty) : Ty :=
  match T with
  | Ty_Var Y => 
    if X =? Y then S else Ty_Var Y
  | Ty_Fun T1 T2 =>
    Ty_Fun (substituteT X S T1) (substituteT X S T2)
  | Ty_IFix F T =>
    Ty_IFix (substituteT X S F) (substituteT X S T)
  | Ty_Forall bY K T' =>
    Ty_Forall bY K (substituteT (1 + X) (shift_ty S) T')
  | Ty_Builtin u => 
    Ty_Builtin u
  | Ty_Lam bY K1 T' =>
    Ty_Lam bY K1 (substituteT (1 + X) (shift_ty S) T')
  | Ty_App T1 T2 =>
    Ty_App (substituteT X S T1) (substituteT X S T2)
  end.

Definition substituteT_reduc (X : binderTyname) (S T : Ty) : Ty := substituteT 0 S T.

Definition fromDecl (tvd : TVDecl) : Context :=
  match tvd with
  | TyVarDecl v K => K :K: empty
  end.
    
Definition unwrapIFix (F : Ty) (X : binderTyname) (K : Kind) (T : Ty) : Ty := (Ty_App (Ty_App F (Ty_Lam tt K (Ty_IFix F (Ty_Var 0)))) T).

Definition has_kind__DeBruijn : Context -> Ty -> Kind -> Prop := has_kind tyname binderTyname Context lookupK extendK.

Notation "ctx '|-*' T ':' K" := (has_kind tyname binderTyname Context lookupK extendK ctx T K) (at level 40, T at level 0, K at level 0).

Definition has_type__DeBruijn : Context -> Term -> Ty -> Prop := has_type name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinTy substituteT_reduc listOfArgumentTypes unwrapIFix.

Notation "ctx '|-+' tm ':' T" := (has_type name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinTy substituteT_reduc listOfArgumentTypes unwrapIFix ctx tm T) (at level 40, tm at level 0, T at level 0).

Definition EqT__DeBruijn : Ty -> Ty -> Prop := EqT tyname binderTyname substituteT_reduc.

Notation "T1 '=b' T2" := (EqT tyname binderTyname substituteT T1 T2) (at level 40).

Definition constructor_well_formed__DeBruijn : Context -> constructor -> Prop := constructor_well_formed name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinTy substituteT_reduc listOfArgumentTypes unwrapIFix.

Notation "ctx '|-ok_c' c" := (constructor_well_formed name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinTy substituteT_reduc listOfArgumentTypes unwrapIFix ctx c) (at level 40, c at level 0).

Definition binding_well_formed__DeBruijn : Context -> Binding -> Prop := binding_well_formed name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinTy substituteT_reduc listOfArgumentTypes unwrapIFix.

Notation "ctx '|-ok' tm" := (binding_well_formed name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinTy substituteT_reduc listOfArgumentTypes unwrapIFix ctx tm) (at level 40, tm at level 0).