From PlutusCert Require Import
  PlutusIR
  Util
.

From PlutusCert Require Import Equality.


Module DumpNotations.
  Require Export Coq.Strings.String.
  Require Export Coq.Strings.Byte.
  Require Export Coq.ZArith.BinInt.

  Notation ":|" := (cons).
  Notation ":" := (cons).
  Notation "()" := (tt).
  Notation "[]" := (nil).

  Definition const {A} (x : A) (y : unit) : A := x.

  Definition TyFun := const Ty_Fun.
  Definition TyApp := const Ty_App.
  Definition TyVar := const Ty_Var.
  Definition TyForall := const Ty_Forall.
  Definition TyBuiltin := const Ty_Builtin.
  Definition TyLam := const Ty_Lam.
  Definition TyIFix := const Ty_IFix.

  Definition KindArrow := const Kind_Arrow.

  Definition Name (s : string) (n : nat) := string_of_nat n.
  Definition TyName (s : string) := s.
  Definition Unique (n : nat) := n.

  Definition SomeTypeIn (T : DefaultUni) := T.
  Definition DefaultUniData := DefaultUniBool. (* update DefaultUni *)


  Definition Datatype := const PlutusIR.Datatype.

  Definition TyVarDecl := const TyVarDecl.
  Definition VarDecl := const VarDecl.

  Definition Let := const Let.
  Definition Var := const Var.
  Definition TyAbs := const TyAbs.
  Definition LamAbs := const LamAbs.
  Definition Apply := const Apply.
  Definition Constant := const Constant.
  Definition Builtin := const Builtin.
  Definition TyInst := const TyInst.
  Definition Error := const Error.
  Definition IWrap := const IWrap.
  Definition Unwrap := const Unwrap.
  Definition Constr := const Constr.
  Definition Case := const Case.
  Definition TermBind := const TermBind.
  Definition TypeBind := const TypeBind.
  Definition DatatypeBind := const DatatypeBind.

  Definition True := true.
  Definition False := false.

  Definition Kind_Base := const Kind_Base.
  Definition Some {A} (x : A) := x.

  Definition SrcSpans (x : list src_span) := x.

  Definition Word8 (b : byte) := b.

  #[global]
  Notation "'Set' x" := (x) (at level 10).
  #[global]
  Notation "'Type'" := (Kind_Base).

  (* Set Warnings "-abstract-large-number". *)

  Open Scope string_scope.
  Open Scope byte_scope.
  Open Scope Z_scope.

  Arguments Word8 _%byte_scope.
  Import Strings.Byte.
  Definition byte_to_Z b := Z.of_nat (Byte.to_nat b).
  Definition byte_of_Z x := of_nat (Z.to_nat x).
  Number Notation byte byte_of_Z byte_to_Z : byte_scope.


  Number Notation nat Nat.of_num_uint Nat.to_num_hex_uint (abstract after 0) : hex_nat_scope.
  Number Notation nat Nat.of_num_uint Nat.to_num_uint (abstract after 0) : nat_scope.

  #[export]
  Set Warnings "-abstract-large-number".

End DumpNotations.





Section Parsing_examples.

  Import DumpNotations.

  Definition Original {A} := fun (x : A) => tt.

  Definition t_test := (Let (Original (Ann MayInline (SrcSpans (Set [])))) NonRec (:| (TermBind (Original (Ann MayInline (SrcSpans (Set [])))) Strict (VarDecl (Original (Ann MayInline (SrcSpans (Set [])))) (Name "unsafeDataAsMap" (Unique 7632)) (TyFun (Original (Ann MayInline (SrcSpans (Set [])))) (TyBuiltin (Original (Ann MayInline (SrcSpans (Set [])))) ((DefaultUniData))) (TyApp (Original (Ann MayInline (SrcSpans (Set [])))) (TyBuiltin (Original (Ann MayInline (SrcSpans (Set [])))) ((DefaultUniProtoList))) (TyApp (Original (Ann MayInline (SrcSpans (Set [])))) (TyApp (Original (Ann MayInline (SrcSpans (Set [])))) (TyBuiltin (Original (Ann MayInline (SrcSpans (Set [])))) ((DefaultUniProtoPair))) (TyBuiltin (Original (Ann MayInline (SrcSpans (Set [])))) ((DefaultUniData)))) (TyBuiltin (Original (Ann MayInline (SrcSpans (Set [])))) ((DefaultUniData))))))) (Builtin (Original (Ann MayInline (SrcSpans (Set [])))) UnMapData)) [])).


  Open Scope string_scope.
  Require Import Coq.ZArith.BinInt.
  Open Scope Z_scope.

  Definition x : Z := 10.
  Set Warnings "-abstract-large-number".

(*  Eval vm_compute in (Term_eqb large2 large2). *)

End Parsing_examples.

Section Computing_asts.
  Import DumpNotations.
  Definition bindings : list binding :=
  (:| (DatatypeBind () (Datatype () (TyVarDecl () (TyName (Name "Credential" (Unique 158100))) (Kind_Base ())) [] (Name "Credential_match" (Unique 158103)) (: (VarDecl () (Name "PubKeyCredential" (Unique 158101)) (TyFun () (TyBuiltin () (SomeTypeIn DefaultUniByteString)) (TyVar () (TyName (Name "Credential" (Unique 158100)))))) (: (VarDecl () (Name "ScriptCredential" (Unique 158102)) (TyFun () (TyBuiltin () (SomeTypeIn DefaultUniByteString)) (TyVar () (TyName (Name "Credential" (Unique 158100)))))) [])))) (: (DatatypeBind () (Datatype () (TyVarDecl () (TyName (Name "StakingCredential" (Unique 158104))) (Kind_Base ())) [] (Name "StakingCredential_match" (Unique 158107)) (: (VarDecl () (Name "StakingHash" (Unique 158105)) (TyFun () (TyVar () (TyName (Name "Credential" (Unique 158100)))) (TyVar () (TyName (Name "StakingCredential" (Unique 158104)))))) (: (VarDecl () (Name "StakingPtr" (Unique 158106)) (TyFun () (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyFun () (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyFun () (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyVar () (TyName (Name "StakingCredential" (Unique 158104)))))))) [])))) (: (DatatypeBind () (Datatype () (TyVarDecl () (TyName (Name "Maybe" (Unique 158087))) (KindArrow () (Kind_Base ()) (Kind_Base ()))) (: (TyVarDecl () (TyName (Name "a" (Unique 158091))) (Kind_Base ())) []) (Name "Maybe_match" (Unique 158090)) (: (VarDecl () (Name "Just" (Unique 158088)) (TyFun () (TyVar () (TyName (Name "a" (Unique 158091)))) (TyApp () (TyVar () (TyName (Name "Maybe" (Unique 158087)))) (TyVar () (TyName (Name "a" (Unique 158091))))))) (: (VarDecl () (Name "Nothing" (Unique 158089)) (TyApp () (TyVar () (TyName (Name "Maybe" (Unique 158087)))) (TyVar () (TyName (Name "a" (Unique 158091)))))) [])))) (: (DatatypeBind () (Datatype () (TyVarDecl () (TyName (Name "Address" (Unique 158108))) (Kind_Base ())) [] (Name "Address_match" (Unique 158110)) (: (VarDecl () (Name "Address" (Unique 158109)) (TyFun () (TyVar () (TyName (Name "Credential" (Unique 158100)))) (TyFun () (TyApp () (TyVar () (TyName (Name "Maybe" (Unique 158087)))) (TyVar () (TyName (Name "StakingCredential" (Unique 158104))))) (TyVar () (TyName (Name "Address" (Unique 158108))))))) []))) (: (DatatypeBind () (Datatype () (TyVarDecl () (TyName (Name "OutputDatum" (Unique 158095))) (Kind_Base ())) [] (Name "OutputDatum_match" (Unique 158099)) (: (VarDecl () (Name "NoOutputDatum" (Unique 158096)) (TyVar () (TyName (Name "OutputDatum" (Unique 158095))))) (: (VarDecl () (Name "OutputDatum" (Unique 158097)) (TyFun () (TyBuiltin () (SomeTypeIn DefaultUniData)) (TyVar () (TyName (Name "OutputDatum" (Unique 158095)))))) (: (VarDecl () (Name "OutputDatumHash" (Unique 158098)) (TyFun () (TyBuiltin () (SomeTypeIn DefaultUniByteString)) (TyVar () (TyName (Name "OutputDatum" (Unique 158095)))))) []))))) (: (DatatypeBind () (Datatype () (TyVarDecl () (TyName (Name "Tuple2" (Unique 157758))) (KindArrow () (Kind_Base ()) (KindArrow () (Kind_Base ()) (Kind_Base ())))) (: (TyVarDecl () (TyName (Name "a" (Unique 157761))) (Kind_Base ())) (: (TyVarDecl () (TyName (Name "b" (Unique 157762))) (Kind_Base ())) [])) (Name "Tuple2_match" (Unique 157760)) (: (VarDecl () (Name "Tuple2" (Unique 157759)) (TyFun () (TyVar () (TyName (Name "a" (Unique 157761)))) (TyFun () (TyVar () (TyName (Name "b" (Unique 157762)))) (TyApp () (TyApp () (TyVar () (TyName (Name "Tuple2" (Unique 157758)))) (TyVar () (TyName (Name "a" (Unique 157761))))) (TyVar () (TyName (Name "b" (Unique 157762)))))))) []))) []))))))
  .
  Open Scope string_scope.
  Definition let_bindings := Let () NonRec bindings (Error () (Ty_Var "x")).
  (* Very slow: 11 sec. Perhaps the integer conversion causes this. (see warning
  * "abstract-large-number" *)

  (*
  Eval cbv in (Term_eqb let_bindings let_bindings).
  *)

  (* Fast: *)
  Eval vm_compute in (Term_eqb let_bindings let_bindings).

  Definition test : Term_eqb let_bindings let_bindings = true.
  Proof.
    vm_compute. (* necessary to avoid slow notation (or big integer?) computation *)
    reflexivity.
  Qed.

  Open Scope list_scope.
  (*
  Definition let_bindings2 := Let NonRec
         (DatatypeBind
            (Datatype (TyVarDecl "158100" Kind_Base) nil "158103"
               (VarDecl "158101"
                  (Ty_Fun (Ty_Builtin DefaultUniByteString)
                     (Ty_Var "158100"))
                :: VarDecl "158102"
                     (Ty_Fun
                        (Ty_Builtin DefaultUniByteString)
                        (Ty_Var "158100")) :: nil))
          :: DatatypeBind
               (Datatype (TyVarDecl "158104" Kind_Base) nil "158107"
                  (VarDecl "158105"
                     (Ty_Fun (Ty_Var "158100") (Ty_Var "158104"))
                   :: VarDecl "158106"
                        (Ty_Fun
                           (Ty_Builtin DefaultUniInteger)
                           (Ty_Fun
                              (Ty_Builtin DefaultUniInteger)
                              (Ty_Fun
                                 (Ty_Builtin
                                    DefaultUniInteger)
                                 (Ty_Var "158104")))) :: nil))
             :: DatatypeBind
                  (Datatype
                     (TyVarDecl "158087" (Kind_Arrow Kind_Base Kind_Base))
                     (TyVarDecl "158091" Kind_Base :: nil) "158090"
                     (VarDecl "158088"
                        (Ty_Fun (Ty_Var "158091")
                           (Ty_App (Ty_Var "158087") (Ty_Var "158091")))
                      :: VarDecl "158089"
                           (Ty_App (Ty_Var "158087") (Ty_Var "158091"))
                         :: nil))
                :: DatatypeBind
                     (Datatype (TyVarDecl "158108" Kind_Base) nil "158110"
                        (VarDecl "158109"
                           (Ty_Fun (Ty_Var "158100")
                              (Ty_Fun
                                 (Ty_App (Ty_Var "158087") (Ty_Var "158104"))
                                 (Ty_Var "158108"))) :: nil))
                   :: DatatypeBind
                        (Datatype (TyVarDecl "158095" Kind_Base) nil "158099"
                           (VarDecl "158096" (Ty_Var "158095")
                            :: VarDecl "158097"
                                 (Ty_Fun
                                    (Ty_Builtin
                                       DefaultUniBool)
                                    (Ty_Var "158095"))
                               :: VarDecl "158098"
                                    (Ty_Fun
                                       (Ty_Builtin
                                          DefaultUniByteString)
                                       (Ty_Var "158095")) :: nil))
                      :: DatatypeBind
                           (Datatype
                              (TyVarDecl "157758"
                                 (Kind_Arrow Kind_Base
                                    (Kind_Arrow Kind_Base Kind_Base)))
                              (TyVarDecl "157761" Kind_Base
                               :: TyVarDecl "157762" Kind_Base :: nil)
                              "157760"
                              (VarDecl "157759"
                                 (Ty_Fun (Ty_Var "157761")
                                    (Ty_Fun (Ty_Var "157762")
                                       (Ty_App
                                          (Ty_App
                                             (Ty_Var "157758")
                                             (Ty_Var "157761"))
                                          (Ty_Var "157762")))) :: nil))
                         :: nil) (Error (Ty_Var "x"))
  .

  Eval cbv in (Term_eqb let_bindings2 let_bindings2).
  *)

End Computing_asts.
