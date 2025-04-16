Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
From PlutusCert Require Import Analysis.BoundVars.

Require Export PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.Normalisation.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.PlutusIR.Semantics.Static.Builtins.Signatures.

Import Coq.Lists.List.
Import ListNotations.
Import Coq.Strings.String.
Local Open Scope string_scope.

(* Common built-in types *)
Definition Ty_Int := Ty_Builtin DefaultUniInteger.
Definition Ty_Bool := Ty_Builtin DefaultUniBool.
Definition Ty_String := Ty_Builtin DefaultUniString.
Definition Ty_Unit := Ty_Builtin DefaultUniUnit.
Definition Ty_BS := Ty_Builtin DefaultUniByteString.

Definition Ty_BinOp t := Ty_Fun t (Ty_Fun t t).
Definition Ty_BinPred t := Ty_Fun t (Ty_Fun t Ty_Bool).

(** Types of builtin functions *)
Definition lookupBuiltinTy f := to_ty (to_sig f).


(** Helper funcitons*)
Definition flatten {A : Type} (l : list (list A)) := List.concat (rev l).

Open Scope list_scope.
Lemma flatten_cons {A} x (xs : list (list A)) :
  flatten (x :: xs) = flatten xs ++ x.
Proof.
  unfold flatten. simpl.
  rewrite concat_app. simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Definition fromDecl (tvd : tvdecl) : string * kind :=
  match tvd with
  | TyVarDecl v K => (v, K)
  end.

Definition unwrapIFix (F : ty) (K : kind) (T : ty) : ty := (Ty_App (Ty_App F (Ty_Lam "X" K (Ty_IFix F (Ty_Var "X")))) T).

(** Typing of terms *)
Reserved Notation "Delta ',,' Gamma '|-+' t ':' T" (at level 101, t at level 0, T at level 0, no associativity).
Reserved Notation "Delta '|-ok_c' c ':' T" (at level 101, c at level 0, T at level 0).
Reserved Notation "Delta ',,' Gamma  '|-oks_nr' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-oks_r' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-ok_b' b" (at level 101, b at level 0, no associativity).

Local Open Scope list_scope.

Inductive has_type : list (string * kind) -> list (string * ty) -> term -> ty -> Prop :=
  (* Simply typed lambda caclulus *)
  | T_Var : forall Γ Δ x T Tn,
      lookup x Γ = Coq.Init.Datatypes.Some T ->
      normalise T Tn ->
      Δ ,, Γ |-+ (Var x) : Tn
  | T_LamAbs : forall Δ Γ x T1 t T2n T1n,
      Δ |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Δ ,, (x, T1n) :: Γ |-+ t : T2n ->
      Δ ,, Γ |-+ (LamAbs x T1 t) : (Ty_Fun T1n T2n)
  | T_Apply : forall Δ Γ t1 t2 T1n T2n,
      Δ ,, Γ |-+ t1 : (Ty_Fun T1n T2n) ->
      Δ ,, Γ |-+ t2 : T1n ->
      Δ ,, Γ |-+ (Apply t1 t2) : T2n
  (* Universal types *)
  | T_TyAbs : forall Δ Γ X K t Tn,
      ((X, K) :: Δ) ,, Γ |-+ t : Tn ->
      Δ ,, Γ |-+ (TyAbs X K t) : (Ty_Forall X K Tn)
  | T_TyInst : forall Δ Γ t1 T2 T1n X K2 T0n T2n,
      Δ ,, Γ |-+ t1 : (Ty_Forall X K2 T1n) ->
      Δ |-* T2 : K2 ->
      normalise T2 T2n ->
      normalise (substituteTCA X T2n T1n) T0n ->
      Δ ,, Γ |-+ (TyInst t1 T2) : T0n
  (* Recursive types *)
  | T_IWrap : forall Δ Γ F T M K Tn Fn T0n,
      Δ |-* T : K ->
      normalise T Tn ->
      Δ |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      normalise F Fn ->
      normalise (unwrapIFix Fn K Tn) T0n ->
      Δ ,, Γ |-+ M : T0n ->
      Δ ,, Γ |-+ (IWrap F T M) : (Ty_IFix Fn Tn)
  | T_Unwrap : forall Δ Γ M Fn K Tn T0n,
      Δ ,, Γ |-+ M : (Ty_IFix Fn Tn) ->
      Δ |-* Tn : K ->
      normalise (unwrapIFix Fn K Tn) T0n ->
      Δ ,, Γ |-+ (Unwrap M) : T0n
  (* Additional constructs *)
  | T_Constant : forall Δ Γ T a,
      Δ ,, Γ |-+ (Constant (ValueOf T a)) : (Ty_Builtin T)
  | T_Builtin : forall Δ Γ f T Tn,
      T = lookupBuiltinTy f ->
      normalise T Tn ->
      Δ ,, Γ |-+ (Builtin f) : Tn
  | T_Error : forall Δ Γ S T Tn,
      Δ |-* T : Kind_Base ->
      normalise T Tn ->
      Δ ,, Γ |-+ (Error S) : Tn
  (** Let-bindings
      Note: The rules for let-constructs differ significantly from the paper definitions
      because we had to adapt the typing rules to the compiler implementation of type checking.
      Reference: The Haskell module PlutusIR.TypeCheck.Internal in the
      iohk/plutus/plutus-core/plutus-ir project.
  **)
  | T_Let : forall Δ Γ bs t Tn Δ' Γ' bsGn,
      Δ' = flatten (map binds_Delta bs) ++ Δ ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn ->
      Γ' = bsGn ++ Γ ->
      Δ ,, Γ |-oks_nr bs ->
      Δ' ,, Γ' |-+ t : Tn ->
      Δ |-* Tn : Kind_Base ->
      Δ ,, Γ |-+ (Let NonRec bs t) : Tn
  | T_LetRec : forall Δ Γ bs t Tn Δ' Γ' bsGn,
      (* There can be no duplicate bound variables in a let-rec *)
      NoDup (btvbs bs) ->
      NoDup (bvbs bs) ->

      Δ' = flatten (map binds_Delta bs) ++ Δ ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn ->
      Γ' = bsGn ++ Γ->
      Δ' ,, Γ' |-oks_r bs ->
      Δ' ,, Γ' |-+ t : Tn ->
      Δ |-* Tn : Kind_Base ->
      Δ ,, Γ |-+ (Let Rec bs t) : Tn

(* Constructors are well-formed if their result type equals the fully applied
 * datatype (e.g. Either a b), and all parameter types are well-kinded
*)
with constructor_well_formed : list (string * kind) -> vdecl -> ty -> Prop :=
  | W_Con : forall Δ x T Targs Tr Tres,
      (Targs, Tres) = splitTy T ->
      (* We don't check the well-kindedness of Tres, this happens in
         W_Data (since the kind context needs to be slightly larger) *)
      (forall Ta, In Ta Targs -> Δ |-* Ta : Kind_Base) ->
      Tres = Tr ->
      Δ |-ok_c (VarDecl x T) : Tr

with bindings_well_formed_nonrec : list (string * kind) -> list (string * ty) -> list binding -> Prop :=
  | W_NilB_NonRec : forall Δ Γ,
      Δ ,, Γ |-oks_nr nil
  | W_ConsB_NonRec : forall Δ Γ b bs bsGn,
      Δ ,, Γ |-ok_b b ->
      map_normalise (binds_Gamma b) bsGn ->
      ((binds_Delta b) ++ Δ) ,, (bsGn ++ Γ) |-oks_nr bs ->
      Δ ,, Γ |-oks_nr (b :: bs)

with bindings_well_formed_rec : list (string * kind) -> list (string * ty) -> list binding -> Prop :=
  | W_NilB_Rec : forall Δ Γ,
      Δ ,, Γ |-oks_r nil
  | W_ConsB_Rec : forall Δ Γ b bs,
      Δ ,, Γ |-ok_b b ->
      Δ ,, Γ |-oks_r bs ->
      Δ ,, Γ |-oks_r (b :: bs)

with binding_well_formed : list (string * kind) -> list (string * ty) -> binding -> Prop :=
  | W_Term : forall Δ Γ s x T t Tn,
      Δ |-* T : Kind_Base ->
      normalise T Tn ->
      Δ ,, Γ |-+ t : Tn ->
      Δ ,, Γ |-ok_b (TermBind s (VarDecl x T) t)
  | W_Type : forall Δ Γ X K T,
      Δ |-* T : K ->
      Δ ,, Γ |-ok_b (TypeBind (TyVarDecl X K) T)
  | W_Data : forall Δ Γ dtd XK YKs matchFunc cs X Ys Δ' Tres,
      dtd = Datatype XK YKs matchFunc cs ->
      X = tvdecl_name XK ->
      Ys = map tvdecl_name YKs ->

      (* No duplicate bound type variables *)
      NoDup (X :: Ys) ->

      (* No duplicate constructor names*)
      NoDup (map vdecl_name cs) ->

      (* Well-formedness of constructors *)
      Δ' = rev (map fromDecl YKs) ++ Δ ->
      Tres = constrLastTyExpected dtd -> (* The expected result type for each constructor *)
      (forall c, In c cs -> Δ' |-ok_c c : Tres) ->

      (* The expected result type is well-kinded *)
      (* In the case that this DatatypeBind is in a let-rec, X will already be
       * in Δ, but it is not problematic to add it another time. It is needed
       * for non-recursive DatatypeBinds
       *)
      (fromDecl XK :: Δ') |-* Tres : Kind_Base ->

      Δ ,, Γ |-ok_b (DatatypeBind dtd)

  where "Δ ',,' Γ '|-+' t ':' T" := (has_type Δ Γ t T)
  and  "Δ '|-ok_c' c ':' T" := (constructor_well_formed Δ c T)
  and "Δ ',,' Γ '|-oks_nr' bs" := (bindings_well_formed_nonrec Δ Γ bs)
  and "Δ ',,' Γ '|-oks_r' bs" := (bindings_well_formed_rec Δ Γ bs)
  and "Δ ',,' Γ '|-ok_b' b" := (binding_well_formed Δ Γ b).

Scheme has_type__ind := Minimality for has_type Sort Prop
  with constructor_well_formed__ind := Minimality for constructor_well_formed Sort Prop
  with bindings_well_formed_nonrec__ind := Minimality for bindings_well_formed_nonrec Sort Prop
  with bindings_well_formed_rec__ind := Minimality for bindings_well_formed_rec Sort Prop
  with binding_well_formed__ind := Minimality for binding_well_formed Sort Prop.

Combined Scheme has_type__multind from
  has_type__ind,
  bindings_well_formed_nonrec__ind,
  bindings_well_formed_rec__ind,
  binding_well_formed__ind.

Definition well_typed t := exists T, [] ,, [] |-+ t : T.

(* I think we can make a non-recursive let with a constructor refering to a previous term 

So maybe we create WeirdList with non-rec let
WeirdList:
 cons: WeirdList -> WeirdList
  nil: WeirdList
*)

Definition mydtd :=
  DatatypeBind (Datatype (TyVarDecl "WeirdList" Kind_Base) [] "WeirdListMatch" 
  (* and then constructors *)
    [
      VarDecl "nil" (Ty_Var "WeirdList");
      VarDecl "cons" (Ty_Fun (Ty_Var "WeirdList") (Ty_Var "WeirdList"))
    ]
  )
.

Definition my_other_weirdList :=
  TypeBind (TyVarDecl "WeirdList" Kind_Base) (Ty_Builtin DefaultUniInteger).

Definition myWeirdTerm :=
  Let NonRec [my_other_weirdList]
    (Let NonRec [mydtd] 
      (
        (Var "x")
      )).

Search "map_normalise".

Lemma myWeirdTerm__well_typed :
  nil ,, [("x", (Ty_Builtin DefaultUniInteger))] |-+ myWeirdTerm : (Ty_Builtin DefaultUniInteger).
Proof.
  unfold myWeirdTerm.
  econstructor; eauto.
  - unfold my_other_weirdList.
    econstructor; eauto.
    + constructor.
      constructor.
      constructor.
    + constructor.
  - unfold mydtd.
    eapply T_Let with (bsGn := (flatten (map binds_Gamma [DatatypeBind (Datatype
  (TyVarDecl "WeirdList" Kind_Base) [] "WeirdListMatch"
  [VarDecl "nil"
  (Ty_Var
  "WeirdList");
  VarDecl "cons"
  (Ty_Fun
  (Ty_Var
  "WeirdList")
  (Ty_Var
  "WeirdList"))])]))).
    econstructor; eauto.
    + repeat constructor.
    + eauto.
    + apply W_ConsB_NonRec with (bsGn := (binds_Gamma
          (DatatypeBind
          (Datatype (TyVarDecl "WeirdList"
          Kind_Base) [] "WeirdListMatch"
          [VarDecl "nil" (Ty_Var "WeirdList");
          VarDecl "cons"
          (Ty_Fun (Ty_Var "WeirdList") (Ty_Var "WeirdList"))])))); eauto.
      * eapply W_Data with (XK := (TyVarDecl "WeirdList" Kind_Base)) (YKs := nil) (cs := [VarDecl "nil" (Ty_Var "WeirdList");
  VarDecl "cons"
  (Ty_Fun (Ty_Var "WeirdList")
  (Ty_Var "WeirdList"))]) (matchFunc := "WeirdListMatch"); eauto.
        -- constructor. simpl. auto. constructor.
        -- simpl. constructor. intuition. inversion H. inversion H0. inversion H0. constructor. intuition. constructor.
        -- intros.
            (* checking both constructors *)
           induction H; subst.
           ++ simpl.
              econstructor; eauto.
              unfold splitTy; eauto.
              intros.
              inversion H.
           ++ induction H; subst; [|inversion H].
              simpl.
              econstructor; eauto.
              simpl; eauto.
              intros.
              inversion H; [|inversion H0].
              subst.
              constructor.
              auto.
        -- (* 
              We have a constraint that all argument types must be kind base, so the shadowed type
                must always be of kind_base
          *)
           simpl.
           constructor.
           auto.
      * (* map_normalise refl *)
        repeat constructor.
      * constructor.
    + eapply T_Var; eauto.
      constructor.
    + constructor.
      constructor.
  - constructor.
    constructor.
Qed.


Lemma T_Let__cons Δ Γ Γ_b b bs t Tn :
  Δ ,, Γ |-ok_b b ->
  Δ |-* Tn : Kind_Base -> (* Tn may not mention types bound in b (escaping) *)
  map_normalise (binds_Gamma b) Γ_b ->
  binds_Delta b ++ Δ ,, Γ_b ++ Γ |-+ (Let NonRec bs t) : Tn ->
  Δ ,, Γ |-+ (Let NonRec (b :: bs) t) : Tn
.
Proof.
  intros H_typing_b H_kind H_mn H_ty.
  inversion H_ty; subst.

  econstructor.
  - exact eq_refl.
  - unfold flatten.
    simpl.
    rewrite concat_app.
    simpl.
    rewrite app_nil_r.
    apply MN_app.
    + eassumption.
    + eassumption.
  - exact eq_refl.
  - econstructor.
    + assumption.
    + eassumption.
    + eassumption.
  - simpl.
    rewrite flatten_cons.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    assumption.
  - assumption.
Qed.

Lemma has_type__normal : forall Delta Gamma t T,
    Delta ,, Gamma |-+ t : T ->
    normal_Ty T.
Proof with eauto.
  induction 1; intros; eauto using normalise_to_normal...
  - inversion IHhas_type1; subst...
    inversion H1.
Qed.


(* ↪ = \hookrightarrow *)
Reserved Notation "Δ1 ',,' Γ1 '|-' C ':' HTy ↪ T1"
  (at level 101, C at level 0, T1 at level 0, no associativity).

(* Typing rules for one-hole contexts *)
Inductive context_has_type : list (string * kind) -> list (string * ty) -> context -> ((list (string * kind)) * list (string * ty) * ty) -> ty -> Prop :=

  | T_C_Hole : forall Δ Γ Tn,
      normal_Ty Tn ->
      Δ ,, Γ |- C_Hole : (Δ, Γ, Tn) ↪ Tn

  | T_C_LamAbs : forall Δ1 Γ1 x T1 C Δ Γ Tn T2n T1n,
      Δ1 |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Δ1 ,, (x, T1n) :: Γ1 |- C                 : (Δ , Γ, Tn) ↪ T2n ->
      Δ1 ,,             Γ1 |- (C_LamAbs x T1 C) : (Δ , Γ, Tn) ↪ (Ty_Fun T1n T2n)

  | T_C_Apply_L : forall Δ1 Γ1 Δ Γ C t Tn T1n T2n,
      Δ1 ,, Γ1 |- C : (Δ , Γ, Tn) ↪ (Ty_Fun T1n T2n) ->
      Δ1 ,, Γ1 |-+ t : T1n ->
      Δ1 ,, Γ1 |- (C_Apply_L C t) : (Δ , Γ, Tn) ↪ T2n

  | T_C_Apply_R : forall Δ1 Γ1 Δ Γ C t Tn T1n T2n,
      Δ1 ,, Γ1 |-+ t : (Ty_Fun T1n T2n) ->
      Δ1 ,, Γ1 |- C : (Δ , Γ, Tn) ↪ T1n ->
      Δ1 ,, Γ1 |- (C_Apply_R t C) : (Δ , Γ, Tn) ↪ T2n

  where
    "Δ1 ',,' Γ1 '|-' C ':' Hty ↪ T1" := (context_has_type Δ1 Γ1 C Hty T1)
.

Lemma context_has_type__normal : forall Δ1 Γ1 C Δ Γ T T1,
    Δ1 ,, Γ1 |- C : (Δ , Γ, T) ↪ T1 ->
    normal_Ty T1.
Proof with eauto using normalise_to_normal.
  intros Δ1 Γ1 C Δ Γ T T1 Cty.
  induction Cty...

  (* C_App_L *)
  - inversion IHCty...
    (* NO_Neutral *)
    + inversion H0.

  (* C_App_R *)
  - apply has_type__normal in H.
    inversion H...
    (* NO_Neutral *)
    + inversion H0.
Qed.

Lemma context_has_type__hole_normal : forall Δ1 Γ1 C Δ Γ T T1,
    Δ1 ,, Γ1 |- C : (Δ , Γ, T) ↪ T1 ->
    normal_Ty T.
Proof.
  intros Δ1 Γ1 C Δ Γ T T1 Cty.
  Require Import Coq.Program.Equality.
  dependent induction Cty.
  all: eauto.
Qed.


Lemma context_has_type__fill C t Δ1 Γ1 Δ Γ T T1 :
  Δ1 ,, Γ1 |- C : (Δ, Γ, T) ↪ T1 ->
  Δ ,, Γ |-+ t : T ->
  Δ1 ,, Γ1 |-+ (context_fill C t) : T1.
Proof.
  intros H_C H_t.
  dependent induction H_C;
  eauto using has_type.
Qed.

Lemma context_comp__has_type
  Δ1 Γ1 C T1
  Δ2 Γ2 C' T2
  Δ Γ T :
    Δ1 ,, Γ1 |- C : (Δ2, Γ2, T2) ↪ T1 ->
    Δ2 ,, Γ2 |- C' : (Δ, Γ, T) ↪ T2 ->
    Δ1 ,, Γ1 |- (context_comp C C') : (Δ, Γ, T) ↪ T1
.
Admitted.
