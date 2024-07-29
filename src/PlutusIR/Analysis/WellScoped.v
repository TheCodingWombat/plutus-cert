From PlutusCert Require Import
  PlutusIR
  Analysis.BoundVars.

Require Import
  Strings.String
  Lists.List
.

Import ListNotations.


Definition ctx := list string.

Reserved Notation "Δ '|-*' T" (at level 40, T at level 0).
Inductive well_scoped_Ty (Δ : ctx) : ty -> Prop :=
  | WST_Var : forall X,
      In X Δ ->
      Δ |-* (Ty_Var X)
  | WST_Fun : forall T1 T2,
      Δ |-* T1 ->
      Δ |-* T2 ->
      Δ |-* (Ty_Fun T1 T2)
  | WST_IFix  : forall F T,
      Δ |-* T ->
      Δ |-* F ->
      Δ |-* (Ty_IFix F T)
  | WST_Forall : forall X K T,
      (X :: Δ) |-* T ->
      Δ |-* (Ty_Forall X K T)
  | WST_Builtin : forall T,
      Δ |-* (Ty_Builtin T)
  | WST_Lam : forall X K1 T,
      (X :: Δ) |-* T ->
      Δ |-* (Ty_Lam X K1 T)
  | WST_App : forall T1 T2,
      Δ |-* T1 ->
      Δ |-* T2 ->
      Δ |-* (Ty_App T1 T2)
where "Δ '|-*' T " := (well_scoped_Ty Δ T).

Reserved Notation "Δ ',,' Γ '|-+' t " (at level 101, t at level 0, no associativity).
Reserved Notation "Δ '|-ws_ok_c' c " (at level 101, c at level 0).
Reserved Notation "Δ ',,' Γ  '|-ws_oks_nr' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Δ ',,' Γ '|-ws_oks_r' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Δ ',,' Γ '|-ws_ok_b' b" (at level 101, b at level 0, no associativity).

Inductive constructor_well_formed (Δ : ctx) : vdecl -> Prop :=
  | W_Con : forall x T,
      Δ |-* T ->
      Δ |-ws_ok_c (VarDecl x T)
  where
    "Δ '|-ws_ok_c' c" := (constructor_well_formed Δ c)
.

Inductive well_scoped (Δ Γ: ctx) : term -> Prop :=
  | WS_Var : forall x,
      In x Γ ->
      Δ ,, Γ |-+ (Var x)
  | WS_LamAbs : forall x T t,
      Δ |-* T ->
      Δ ,, (x :: Γ) |-+ t ->
      Δ ,, Γ |-+ (LamAbs x T t)
  | WS_Apply : forall t1 t2,
      Δ ,, Γ |-+ t1 ->
      Δ ,, Γ |-+ t2 ->
      Δ ,, Γ |-+ (Apply t1 t2)
  (* Universal types *)
  | WS_TyAbs : forall X K t,
      (X :: Δ) ,, Γ |-+ t ->
      Δ ,, Γ |-+ (TyAbs X K t)
  | WS_TyInst : forall t T,
      Δ ,, Γ |-+ t ->
      Δ |-* T ->
      Δ ,, Γ |-+ (TyInst t T)
  | WS_IWrap : forall F T M,
      Δ |-* F ->
      Δ |-* T ->
      Δ ,, Γ |-+ M ->
      Δ ,, Γ |-+ (IWrap F T M)
  | WS_Unwrap : forall M,
      Δ ,, Γ |-+ M ->
      Δ ,, Γ |-+ (Unwrap M)
  | WS_Constant : forall (c : constant),
      Δ ,, Γ |-+ (Constant c)
  | WS_Builtin : forall f,
      Δ ,, Γ |-+ (Builtin f)
  | WS_Error : forall S,
      Δ |-* S ->
      Δ ,, Γ |-+ (Error S)
  | WS_Let : forall bs t Δ' Γ',
      Δ' = rev (btvbs bs) ++ Δ ->
      Γ' = rev (bvbs bs) ++ Γ ->
      Δ ,, Γ |-ws_oks_nr bs ->
      Δ' ,, Γ' |-+ t ->
      Δ ,, Γ |-+ (Let NonRec bs t)
  | WS_LetRec : forall bs t Δ' Γ',
      Δ' = rev (btvbs bs) ++ Δ ->
      Γ' = rev (bvbs bs) ++ Γ ->
      Δ' ,, Γ' |-ws_oks_r bs ->
      Δ' ,, Γ' |-+ t ->
      Δ ,, Γ |-+ (Let Rec bs t)


with bindings_well_formed_nonrec (Δ Γ : ctx) : list binding -> Prop :=

  | W_NilB_NonRec :
    Δ ,, Γ |-ws_oks_nr nil

  | W_ConsB_NonRec : forall b bs,
      Δ ,, Γ |-ws_ok_b b ->
      (btvb b ++ Δ) ,, (bvb b ++ Γ) |-ws_oks_nr bs ->
      Δ ,, Γ |-ws_oks_nr (b :: bs)

with bindings_well_formed_rec (Δ Γ : ctx) : list binding -> Prop :=

  | W_NilB_Rec :
      Δ ,, Γ |-ws_oks_r nil
  | W_ConsB_Rec : forall b bs,
      Δ ,, Γ |-ws_ok_b b ->
      Δ ,, Γ |-ws_oks_r bs ->
      Δ ,, Γ |-ws_oks_r (b :: bs)

with binding_well_formed (Δ Γ : ctx) : binding -> Prop :=
  | W_Term : forall s x T t,
      Δ |-* T ->
      Δ ,, Γ |-+ t ->
      Δ ,, Γ |-ws_ok_b (TermBind s (VarDecl x T) t)
  | W_Type : forall X K T,
      Δ |-* T ->
      Δ ,, Γ |-ws_ok_b (TypeBind (TyVarDecl X K) T)
  | W_Data : forall X YKs cs matchFunc Δ',
      Δ' = rev (map tvdecl_name YKs) ++ Δ  ->
      (forall c, In c cs -> Δ' |-ws_ok_c c) ->
      Δ ,, Γ |-ws_ok_b (DatatypeBind (Datatype X YKs matchFunc cs))

  where "Δ ',,' Γ '|-+' t" := (well_scoped Δ Γ t)
  and "Δ ',,' Γ '|-ws_oks_nr' bs" := (bindings_well_formed_nonrec Δ Γ bs)
  and "Δ ',,' Γ '|-ws_oks_r' bs" := (bindings_well_formed_rec Δ Γ bs)
  and "Δ ',,' Γ '|-ws_ok_b' b" := (binding_well_formed Δ Γ b)
.

Definition closed := well_scoped [] [].
