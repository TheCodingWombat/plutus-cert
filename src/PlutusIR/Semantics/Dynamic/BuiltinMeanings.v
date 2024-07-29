Require Import PlutusCert.PlutusIR.
Import ZArith.BinInt.
Import Coq.Lists.List.
Import Coq.Strings.String.
Import Coq.Strings.Byte.
Import Ascii.
Require Import Coq.Strings.BinaryString.
From Equations Require Import Equations.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ** Arity of built-in functions *)
Definition arity (df : DefaultFun) : nat :=
  match df with
  | AddInteger => 2
  | IfThenElse => 4
  | _ => 0 (* TODO: implement lookupBuiltinTy, then this can be calculated from the type *)
  end
  (*
  match df with
  | SubtractInteger => 2
  | MultiplyInteger => 2
  | DivideInteger => 2
  | QuotientInteger => 2
  | RemainderInteger => 2
  | ModInteger => 2
  | LessThanInteger => 2
  | LessThanEqInteger => 2
  | GreaterThanInteger => 2
  | GreaterThanEqInteger => 2
  | EqInteger => 2
  | Concatenate => 2
  | TakeByteString => 2
  | DropByteString => 2
  | SHA2 => 1
  | SHA3 => 1
  | VerifySignature => 3
  | EqByteString => 2
  | LtByteString => 2
  | GtByteString => 2
  | CharToString => 1
  | Append => 2
  | Trace => 1
  end
  *)
.

(** ** Meanings of built-in functions *)

Definition constInt (a : Z) : term := (Constant (ValueOf DefaultUniInteger a)).
Definition constBool (a : bool) : term := Constant (ValueOf DefaultUniBool a).
Definition constBS (a : list byte) : term := Constant (ValueOf DefaultUniByteString a).
(* Definition constChar (a : ascii) : term := Constant (Some' (ValueOf DefaultUniChar a)). *)
Definition constString (a : string) : term := Constant (ValueOf DefaultUniString a).
Definition constUnit (a : unit) : term := Constant (ValueOf DefaultUniUnit a).

Definition take (x : Z) (s : string) : string := substring 0 (Z.to_nat x) s.
Definition drop (x : Z) (s : string) : string := substring (Z.to_nat x) (length s) s.

#[export] Hint Unfold
  constInt
  constBool
  constBS
  (* constChar *)
  constString
  constUnit
  take
  drop
  : core.

(** Computes results of fully applied default functions where possible.

    Note that not all default functions have sensible implementations, such
    as SHA2, SHA3 and VerifySignature. This is bound to change in the future.
*)
Definition compute_defaultfun (t : term) : option term := 
  match t with
  (** Binary operators on integers *)
  (* AddInteger *)
  | (Apply
      (Apply
        (Builtin AddInteger)
        (Constant (ValueOf DefaultUniInteger x))
      )
      (Constant (ValueOf DefaultUniInteger y))
    ) => Some (constInt (x + y))

  (** If-Then-Else *)
  | (Apply
      (Apply
        (Apply
          (TyInst
            (Builtin IfThenElse)
            T
          )
          (Constant (ValueOf DefaultUniBool cond))
        )
        thenBranch
      )
      elseBranch
    ) => Some (if cond then thenBranch else elseBranch)

  | _ => None
  end
  (*
None (* TODO: update to new built-ins set *)

  (* SubtractInteger *)
  | (Apply
      (Apply
        (Builtin SubtractInteger)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniInteger (ValueOf _ y)))
    ) => Some (constInt (x - y))
  (* MultiplyInteger *)
  | (Apply
      (Apply
        (Builtin MultiplyInteger)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniInteger (ValueOf _ y)))
    ) => Some (constInt (x * y))
  (* DivideInteger *)
  | (Apply
      (Apply
        (Builtin DivideInteger)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniInteger (ValueOf _ y)))
    ) => Some (constInt (x / y))
  (* QuotientInteger *)
  | (Apply
      (Apply
        (Builtin QuotientInteger)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniInteger (ValueOf _ y)))
    ) => Some (constInt (x ÷ y))
  (* RemainderInteger *)
  | (Apply
      (Apply
        (Builtin RemainderInteger)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniInteger (ValueOf _ y)))
    ) => Some (constInt (Z.rem x y))
  (* ModInteger *)
  | (Apply
      (Apply
        (Builtin ModInteger)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniInteger (ValueOf _ y)))
    ) => Some (constInt (x mod y))
  (** Binary predicates on integers *)
  (* LessThanInteger*)
  | (Apply
      (Apply
        (Builtin LessThanInteger)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniInteger (ValueOf _ y)))
    ) => Some (constBool (x <? y))
  (* LessThanEqInteger *)
  | (Apply
      (Apply
        (Builtin LessThanEqInteger)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniInteger (ValueOf _ y)))
    ) => Some (constBool (x <=? y))
  (* GreaterThanInteger *)
  | (Apply
      (Apply
        (Builtin GreaterThanInteger)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniInteger (ValueOf _ y)))
    ) => Some (constBool (x >? y))
  (* GreaterThanEqInteger *)
  | (Apply
      (Apply
        (Builtin GreaterThanEqInteger)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniInteger (ValueOf _ y)))
    ) => Some (constBool (x >=? y))
  (* EqInteger *)
  | (Apply
      (Apply
        (Builtin EqInteger)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniInteger (ValueOf _ y)))
    ) => Some (constBool (x =? y))
  (** Bytestring operations *)
  (* Concatenate *)
  | (Apply
      (Apply
        (Builtin Concatenate)
        (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs1)))
      )
      (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs2)))
    ) => Some (constBS (bs1 ++ bs2))
  (* TakeByteString *)
  | (Apply
      (Apply
        (Builtin TakeByteString)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs)))
    ) => Some (constBS (take x bs))
  (* DropByteString *)
  | (Apply
      (Apply
        (Builtin DropByteString)
        (Constant (@Some' _ DefaultUniInteger (ValueOf _ x)))
      )
      (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs)))
    ) => Some (constBS (drop x bs))
  (** Bytestring hashing

      Note: We model hashing by identity. Comparing hashes now becomes a straightforward equality check.
      We believe modelling hash function as such is sufficient, because the dynamic semantics is not meant to
      be used as a basis for a real-world evaluator.
  *)
  | (Apply
      (Builtin SHA2)
      (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs)))
    ) => Some (constBS bs)
  | (Apply
      (Builtin SHA3)
      (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs)))
    ) => Some (constBS bs)
  (** Signature verification

      TODO: Obviously, this should evaluate to true. However, how can we model the verification of signatures?
      Implementation of signature verification:
      https://input-output-hk.github.io/ouroboros-network/cardano-crypto/Crypto-ECC-Ed25519Donna.html
  *)
  | (Apply
      (Apply
        (Apply
          (Builtin VerifySignature)
          (Constant (@Some' _ DefaultUniByteString (ValueOf _ publicKey)))
        )
        (Constant (@Some' _ DefaultUniByteString (ValueOf _ message)))
      )
      (Constant (@Some' _ DefaultUniByteString (ValueOf _ signature)))
    ) => Some (constBool true)
  (** Binary predicates on bytestrings *)
  (* EqByteString *)
  | (Apply
      (Apply
        (Builtin EqByteString)
        (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs1)))
      )
      (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs2)))
    ) => Some (constBool (bs1 =? bs2)%string)
  (* LtByteString *)
  | (Apply
      (Apply
        (Builtin LtByteString)
        (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs1)))
      )
      (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs2)))
    ) => Some (constBool (to_Z bs1 <? to_Z bs2))
  (* GtByteString *)
  | (Apply
      (Apply
        (Builtin GtByteString)
        (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs1)))
      )
      (Constant (@Some' _ DefaultUniByteString (ValueOf _ bs2)))
    ) => Some (constBool (to_Z bs1 >? to_Z bs2))
  (* String operations *)
  (* CharToString *)
  | (Apply
      (Builtin CharToString)
      (Constant (@Some' _ DefaultUniChar (ValueOf _ ch)))
    ) => Some (constString (String ch EmptyString))
  (* Append *)
  | (Apply
      (Apply
        (Builtin Append)
        (Constant (@Some' _ DefaultUniString (ValueOf _ s1)))
      )
      (Constant (@Some' _ DefaultUniString (ValueOf _ s2)))
    ) => Some (constString (s1 ++ s2))
  (* Trace *)
  | (Apply
      (Builtin Trace)
      (Constant (@Some' _ DefaultUniString (ValueOf _ s)))
    ) => Some (constUnit tt)
  (* Catch-all: The argument term is not a fully applied builtin *)
  | _ => None
  end
  *)
.
