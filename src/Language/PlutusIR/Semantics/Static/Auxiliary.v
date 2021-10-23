Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

(** Getters *)
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

(** Auxiliary functions *)
Definition branchTy (c : constructor) (R : Ty) : Ty :=
  match c with
  | Constructor (VarDecl x T) _ => 
    match T with
    | Ty_Fun T1 T2 => Ty_Fun T1 R
    | _ => R
    end
  end.

Definition dataTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    let branchTypes : list Ty := map (fun c => branchTy c (Ty_Var "R")) cs in
    let branchTypesFolded := fold_right (@Ty_Fun tyname binderTyname) (Ty_Var "R") branchTypes in
    let indexKinds := map (fun YK => Ty_Lam (getTyname YK) (getKind YK)) YKs in
    fold_right apply (Ty_Forall "R" Kind_Base branchTypesFolded) indexKinds
  end.

Definition constrLastTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
      let indexTyVars := map (compose (@Ty_Var tyname binderTyname) getTyname) YKs in
      let indexTyVarsAppliedToX := fold_left (@Ty_App tyname binderTyname) indexTyVars (Ty_Var (getTyname X)) in
      indexTyVarsAppliedToX
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

(** Binder functions *)
Definition constrBind (d : DTDecl) (c : constructor) : name * Ty :=
  match d, c with
  | Datatype X YKs matchFunc cs, Constructor (VarDecl x T) _ =>
    (x, constrTy d c)
  end.

Definition constrBinds (d : DTDecl) : list (name * Ty) :=
  match d with
  | Datatype X YKs matchFunc cs =>
    rev (map (constrBind d) cs)
  end.

Definition matchBind (d : DTDecl) : name * Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    (matchFunc, matchTy d)
  end.

Definition binds_Delta (b : Binding) : list (tyname * Kind) :=
  match b with
  | TermBind _ _ _ => nil
  | TypeBind (TyVarDecl X K) ty => (X, K) :: nil
  | DatatypeBind (Datatype (TyVarDecl X K) _ _ _) => (X, K):: nil
  end.

Definition binds_Gamma (b : Binding) : list (name * Ty) :=
  match b with
  | TermBind _ (VarDecl x T) _ => (x, T) :: nil
  | TypeBind _ _ => nil 
  | DatatypeBind d => 
      let constrBs := constrBinds d in
      let matchB := matchBind d in
      matchB :: constrBs
  end.

(*
Definition d' : Binding := 
  DatatypeBind 
    (Datatype 
      (TyVarDecl "EndDate" (Kind_Base))
      nil
      "EndDate_match"
      [ Constructor 
          (VarDecl 
            "Fixed"
            (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var "EndDate"))
          )
          1
      ; Constructor
          (VarDecl 
            "Never" 
            (Ty_Var "EndDate")
          )
          0
      ]
    ).

Compute binds_Delta d'.
Compute binds_Gamma d'.

Definition d : Binding :=
  DatatypeBind 
    (Datatype 
      (TyVarDecl "Maybe" (Kind_Arrow Kind_Base Kind_Base))
      [TyVarDecl "A" (Kind_Base)]
      "matchMaybe"
      [ Constructor 
          (VarDecl
            "Just"
            (Ty_Fun (Ty_Var "A") (Ty_App (Ty_Var "Maybe") (Ty_Var "A")))
          )
          1
      ; Constructor
          (VarDecl
            "Nothing"
            (Ty_Fun (Ty_Var "Maybe") (Ty_Var "A"))
          )
          0
      ]
    ).

Compute binds_Delta d.
Compute binds_Gamma d.


Compute (fun db => match db with | DatatypeBind dtd => constrLastTy dtd | _ => Ty_Var "X" end) d.*)