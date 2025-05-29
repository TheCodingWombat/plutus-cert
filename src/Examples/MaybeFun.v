From PlutusCert Require Import
  PlutusIR Parser
.
Import Parser.DumpNotations.
Open Scope pir_dump_scope.

(*

Adapted the maybeFun from (plutus-tx-plugin/test/Optimization/Spec.hs), so that
it has no escaping in its top-level type (maybeFun has Maybe in its top-level type).

maybeFun' :: CompiledCode Integer
maybeFun' = $$(compile
   [|| let f = \(x :: Maybe Integer) (y :: Maybe Integer) ->
                case x of
                   Just x' -> case y of
                        Just y' -> Just (x' `Builtins.addInteger` y')
                        Nothing -> Nothing
                   Nothing -> Nothing
        in case f (Just 3) (Just 5) of
          Just n -> n
          Nothing -> 0
   ||])

*)

Definition maybeFun__dead_code_eliminated:=

Let () NonRec (TermBind () Strict (VarDecl () (Name
[x61,x64,x64,x49,x6e,x74,x65,x67,x65,x72] (Unique 676)) (TyFun () (TyBuiltin ()
(SomeTypeIn DefaultUniInteger)) (TyFun () (TyBuiltin () (SomeTypeIn
DefaultUniInteger)) (TyBuiltin () (SomeTypeIn DefaultUniInteger))))) (Builtin ()
AddInteger) :| []) (Let () NonRec (TermBind () NonStrict (VarDecl () (Name
[x61,x64,x64,x49,x6e,x74,x65,x67,x65,x72] (Unique 682)) (TyFun () (TyBuiltin ()
(SomeTypeIn DefaultUniInteger)) (TyFun () (TyBuiltin () (SomeTypeIn
DefaultUniInteger)) (TyBuiltin () (SomeTypeIn DefaultUniInteger))))) (LamAbs ()
(Name [x78] (Unique 678)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (LamAbs
() (Name [x79] (Unique 679)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (Let
() NonRec (TermBind () Strict (VarDecl () (Name [x78] (Unique 680)) (TyBuiltin
() (SomeTypeIn DefaultUniInteger))) (Var () (Name [x78] (Unique 678))) :| [])
(Let () NonRec (TermBind () Strict (VarDecl () (Name [x79] (Unique 681))
(TyBuiltin () (SomeTypeIn DefaultUniInteger))) (Var () (Name [x79] (Unique
679))) :| []) (Apply () (Apply () (Var () (Name
[x61,x64,x64,x49,x6e,x74,x65,x67,x65,x72] (Unique 676))) (Var () (Name [x78]
(Unique 680)))) (Var () (Name [x79] (Unique 681)))))))) :| []) (Let () Rec
(DatatypeBind () (Datatype () (TyVarDecl () (TyName (Name "Maybe"
(Unique 683))) (KindArrow () (Type ()) (Type ()))) [TyVarDecl () (TyName (Name
"a" (Unique 687))) (Type ())] (Name
"maybe-match" (Unique 686)) [VarDecl () (Name
"Just" (Unique 684)) (TyFun () (TyVar () (TyName (Name "a" (Unique
687)))) (TyApp () (TyVar () (TyName (Name "Maybe" (Unique 683))))
(TyVar () (TyName (Name "a" (Unique 687)))))),VarDecl () (Name
"Nothing" (Unique 685)) (TyApp () (TyVar () (TyName (Name
"Maybe" (Unique 683)))) (TyVar () (TyName (Name "a" (Unique
687)))))]) :| []) (Let () NonRec (TermBind () NonStrict (VarDecl () (Name [x66]
(Unique 719)) (TyFun () (TyApp () (TyVar () (TyName (Name "Maybe"
(Unique 683)))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (TyFun () (TyApp
() (TyVar () (TyName (Name "Maybe" (Unique 683)))) (TyBuiltin ()
(SomeTypeIn DefaultUniInteger))) (TyApp () (TyVar () (TyName (Name
"Maybe" (Unique 683)))) (TyBuiltin () (SomeTypeIn
DefaultUniInteger)))))) (LamAbs () (Name [x64,x73] (Unique 699)) (TyApp ()
(TyVar () (TyName (Name "Maybe" (Unique 683)))) (TyBuiltin ()
(SomeTypeIn DefaultUniInteger))) (LamAbs () (Name [x64,x73] (Unique 700)) (TyApp
() (TyVar () (TyName (Name "Maybe" (Unique 683)))) (TyBuiltin ()
(SomeTypeIn DefaultUniInteger))) (Let () NonRec (TermBind () Strict (VarDecl ()
(Name [x64,x73] (Unique 701)) (TyApp () (TyVar () (TyName (Name
"Maybe" (Unique 683)))) (TyBuiltin () (SomeTypeIn
DefaultUniInteger)))) (Var () (Name [x64,x73] (Unique 699))) :| []) (Let ()
NonRec (TermBind () Strict (VarDecl () (Name [x64,x73] (Unique 702)) (TyApp ()
(TyVar () (TyName (Name "Maybe" (Unique 683)))) (TyBuiltin ()
(SomeTypeIn DefaultUniInteger)))) (Var () (Name [x64,x73] (Unique 700))) :| [])
(TyInst () (Apply () (Apply () (TyInst () (Apply () (TyInst () (Var () (Name
"maybe-match" (Unique 686))) (TyBuiltin ()
(SomeTypeIn DefaultUniInteger))) (Var () (Name [x64,x73] (Unique 701))))
(TyForall () (TyName (Name "dead" (Unique 706))) (Type ()) (TyApp ()
(TyVar () (TyName (Name "Maybe" (Unique 683)))) (TyBuiltin ()
(SomeTypeIn DefaultUniInteger))))) (LamAbs () (Name "x'" (Unique 707))
(TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyAbs () (TyName (Name
"dead" (Unique 708))) (Type ()) (TyInst () (Apply () (Apply ()
(TyInst () (Apply () (TyInst () (Var () (Name
"maybe-match" (Unique 686))) (TyBuiltin ()
(SomeTypeIn DefaultUniInteger))) (Var () (Name [x64,x73] (Unique 702))))
(TyForall () (TyName (Name "dead" (Unique 712))) (Type ()) (TyApp ()
(TyVar () (TyName (Name "Maybe" (Unique 683)))) (TyBuiltin ()
(SomeTypeIn DefaultUniInteger))))) (LamAbs () (Name "y'" (Unique 713))
(TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyAbs () (TyName (Name
"dead" (Unique 714))) (Type ()) (Apply () (TyInst () (Var () (Name
"Just" (Unique 684))) (TyBuiltin () (SomeTypeIn DefaultUniInteger)))
(Apply () (Apply () (Var () (Name [x61,x64,x64,x49,x6e,x74,x65,x67,x65,x72]
(Unique 682))) (Var () (Name "x'" (Unique 707)))) (Var () (Name "y'"
(Unique 713)))))))) (TyAbs () (TyName (Name "dead" (Unique 715)))
(Type ()) (TyInst () (Var () (Name "Nothing" (Unique 685)))
(TyBuiltin () (SomeTypeIn DefaultUniInteger))))) (TyForall () (TyName (Name
"dead" (Unique 716))) (Type ()) (TyVar () (TyName (Name
"dead" (Unique 716))))))))) (TyAbs () (TyName (Name "dead"
(Unique 717))) (Type ()) (TyInst () (Var () (Name "Nothing"
(Unique 685))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))))) (TyForall ()
(TyName (Name "dead" (Unique 718))) (Type ()) (TyVar () (TyName (Name
"dead" (Unique 718)))))))))) :| []) (Apply () (Apply () (TyInst ()
(Apply () (TyInst () (Var () (Name "maybe-match"
(Unique 686))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (Apply () (Apply
() (Var () (Name [x66] (Unique 719))) (Apply () (TyInst () (Var () (Name
"Just" (Unique 684))) (TyBuiltin () (SomeTypeIn DefaultUniInteger)))
(Constant () (Some (ValueOf DefaultUniInteger 3))))) (Apply () (TyInst () (Var
() (Name "Just" (Unique 684))) (TyBuiltin () (SomeTypeIn
DefaultUniInteger))) (Constant () (Some (ValueOf DefaultUniInteger 5))))))
(TyBuiltin () (SomeTypeIn DefaultUniInteger))) (LamAbs () (Name "n" (Unique
723)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (Var () (Name "n" (Unique
723))))) (Constant () (Some (ValueOf DefaultUniInteger 0)))))))
.


Definition maybeFun__optimised :=

Let () NonRec (DatatypeBind () (Datatype () (TyVarDecl () (TyName (Name
"Maybe" (Unique 1186))) (KindArrow () (Type ()) (Type ())))
[TyVarDecl () (TyName (Name "a" (Unique 1190))) (Type ())] (Name
"maybe-match" (Unique 1189)) [VarDecl () (Name
"Just" (Unique 1187)) (TyFun () (TyVar () (TyName (Name "a" (Unique
1190)))) (TyApp () (TyVar () (TyName (Name "Maybe" (Unique
1186)))) (TyVar () (TyName (Name "a" (Unique 1190)))))),VarDecl () (Name
"Nothing" (Unique 1188)) (TyApp () (TyVar () (TyName (Name
"Maybe" (Unique 1186)))) (TyVar () (TyName (Name "a" (Unique
1190)))))]) :| []) (Constant () (Some (ValueOf DefaultUniInteger 8))).



Require Import Lists.List.
Import ListNotations.
Definition dumps_dce_compile_data : list term :=
[
Let () NonRec (TermBind () Strict (VarDecl () (Name [x61,x64,x64,x49,x6e,x74,x65,x67,x65,x72] (Unique 676)) (TyFun () (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyFun () (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyBuiltin () (SomeTypeIn DefaultUniInteger))))) (Builtin () AddInteger) :| []) (Let () NonRec (TermBind () NonStrict (VarDecl () (Name [x61,x64,x64,x49,x6e,x74,x65,x67,x65,x72] (Unique 682)) (TyFun () (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyFun () (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyBuiltin () (SomeTypeIn DefaultUniInteger))))) (LamAbs () (Name [x78] (Unique 678)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (LamAbs () (Name [x79] (Unique 679)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (Let () NonRec (TermBind () Strict (VarDecl () (Name [x78] (Unique 680)) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (Var () (Name [x78] (Unique 678))) :| []) (Let () NonRec (TermBind () Strict (VarDecl () (Name [x79] (Unique 681)) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (Var () (Name [x79] (Unique 679))) :| []) (Apply () (Apply () (Var () (Name [x61,x64,x64,x49,x6e,x74,x65,x67,x65,x72] (Unique 676))) (Var () (Name [x78] (Unique 680)))) (Var () (Name [x79] (Unique 681)))))))) :| []) (Let () Rec (DatatypeBind () (Datatype () (TyVarDecl () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683))) (KindArrow () (Type ()) (Type ()))) [TyVarDecl () (TyName (Name [x61] (Unique 687))) (Type ())] (Name [x4d,x61,x79,x62,x65,x5f,x6d,x61,x74,x63,x68] (Unique 686)) [VarDecl () (Name [x4a,x75,x73,x74] (Unique 684)) (TyFun () (TyVar () (TyName (Name [x61] (Unique 687)))) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683)))) (TyVar () (TyName (Name [x61] (Unique 687)))))),VarDecl () (Name [x4e,x6f,x74,x68,x69,x6e,x67] (Unique 685)) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683)))) (TyVar () (TyName (Name [x61] (Unique 687)))))]) :| []) (Let () NonRec (TermBind () NonStrict (VarDecl () (Name [x66] (Unique 719)) (TyFun () (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683)))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (TyFun () (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683)))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683)))) (TyBuiltin () (SomeTypeIn DefaultUniInteger)))))) (LamAbs () (Name [x64,x73] (Unique 699)) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683)))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (LamAbs () (Name [x64,x73] (Unique 700)) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683)))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (Let () NonRec (TermBind () Strict (VarDecl () (Name [x64,x73] (Unique 701)) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683)))) (TyBuiltin () (SomeTypeIn DefaultUniInteger)))) (Var () (Name [x64,x73] (Unique 699))) :| []) (Let () NonRec (TermBind () Strict (VarDecl () (Name [x64,x73] (Unique 702)) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683)))) (TyBuiltin () (SomeTypeIn DefaultUniInteger)))) (Var () (Name [x64,x73] (Unique 700))) :| []) (TyInst () (Apply () (Apply () (TyInst () (Apply () (TyInst () (Var () (Name [x4d,x61,x79,x62,x65,x5f,x6d,x61,x74,x63,x68] (Unique 686))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (Var () (Name [x64,x73] (Unique 701)))) (TyForall () (TyName (Name [x64,x65,x61,x64] (Unique 706))) (Type ()) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683)))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))))) (LamAbs () (Name [x78,x27] (Unique 707)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyAbs () (TyName (Name [x64,x65,x61,x64] (Unique 708))) (Type ()) (TyInst () (Apply () (Apply () (TyInst () (Apply () (TyInst () (Var () (Name [x4d,x61,x79,x62,x65,x5f,x6d,x61,x74,x63,x68] (Unique 686))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (Var () (Name [x64,x73] (Unique 702)))) (TyForall () (TyName (Name [x64,x65,x61,x64] (Unique 712))) (Type ()) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 683)))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))))) (LamAbs () (Name [x79,x27] (Unique 713)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyAbs () (TyName (Name [x64,x65,x61,x64] (Unique 714))) (Type ()) (Apply () (TyInst () (Var () (Name [x4a,x75,x73,x74] (Unique 684))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (Apply () (Apply () (Var () (Name [x61,x64,x64,x49,x6e,x74,x65,x67,x65,x72] (Unique 682))) (Var () (Name [x78,x27] (Unique 707)))) (Var () (Name [x79,x27] (Unique 713)))))))) (TyAbs () (TyName (Name [x64,x65,x61,x64] (Unique 715))) (Type ()) (TyInst () (Var () (Name [x4e,x6f,x74,x68,x69,x6e,x67] (Unique 685))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))))) (TyForall () (TyName (Name [x64,x65,x61,x64] (Unique 716))) (Type ()) (TyVar () (TyName (Name [x64,x65,x61,x64] (Unique 716))))))))) (TyAbs () (TyName (Name [x64,x65,x61,x64] (Unique 717))) (Type ()) (TyInst () (Var () (Name [x4e,x6f,x74,x68,x69,x6e,x67] (Unique 685))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))))) (TyForall () (TyName (Name [x64,x65,x61,x64] (Unique 718))) (Type ()) (TyVar () (TyName (Name [x64,x65,x61,x64] (Unique 718)))))))))) :| []) (Apply () (Apply () (TyInst () (Apply () (TyInst () (Var () (Name [x4d,x61,x79,x62,x65,x5f,x6d,x61,x74,x63,x68] (Unique 686))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (Apply () (Apply () (Var () (Name [x66] (Unique 719))) (Apply () (TyInst () (Var () (Name [x4a,x75,x73,x74] (Unique 684))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (Constant () (Some (ValueOf DefaultUniInteger 3))))) (Apply () (TyInst () (Var () (Name [x4a,x75,x73,x74] (Unique 684))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (Constant () (Some (ValueOf DefaultUniInteger 5)))))) (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (LamAbs () (Name [x6e] (Unique 723)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (Var () (Name [x6e] (Unique 723))))) (Constant () (Some (ValueOf DefaultUniInteger 0)))))))
;
Let () NonRec (DatatypeBind () (Datatype () (TyVarDecl () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 1186))) (KindArrow () (Type ()) (Type ()))) [TyVarDecl () (TyName (Name [x61] (Unique 1190))) (Type ())] (Name [x4d,x61,x79,x62,x65,x5f,x6d,x61,x74,x63,x68] (Unique 1189)) [VarDecl () (Name [x4a,x75,x73,x74] (Unique 1187)) (TyFun () (TyVar () (TyName (Name [x61] (Unique 1190)))) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 1186)))) (TyVar () (TyName (Name [x61] (Unique 1190)))))),VarDecl () (Name [x4e,x6f,x74,x68,x69,x6e,x67] (Unique 1188)) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 1186)))) (TyVar () (TyName (Name [x61] (Unique 1190)))))]) :| []) (Constant () (Some (ValueOf DefaultUniInteger 8)))
]
.


From PlutusCert Require Import Typing.Typechecker.
 
Require Import ExtrHaskellZInteger.
(* For strings and chars *)
Require Import ExtrHaskellString.    (* string -> Haskell String, ascii -> Char *)

(* For lists and options *)
Require Import ExtrHaskellBasic.

Parameter show_Z : Z -> string.
Extract Constant show_Z => "show".



(* Tell Coq how to extract pairs to Haskell tuples *)


Extraction Language Haskell.
Redirect "maybeFun.hs" Recursive Extraction dumps_dce_compile_data.