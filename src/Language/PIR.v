From PlutusCert Require Import Language.
From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import Semantics.Dynamic.Bigstep.


Definition PIRLang : Language :=
  {|
    expr  := term
  ; bigstep := fun t t' => exists n, eval t t' n
  ; app   := Apply
  ; const := fun i => Constant (ValueOf DefaultUniInteger i)
  |}
.
