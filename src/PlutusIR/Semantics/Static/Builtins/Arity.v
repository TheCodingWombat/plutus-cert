From PlutusCert Require Import
  PlutusIR.


Definition arity (f : DefaultFun) : nat :=
  match f with
  | AddInteger
  | SubtractInteger
  | MultiplyInteger
  | DivideInteger
  | QuotientInteger => 2

  | EqualsInteger => 2

  | IfThenElse => 4

  | AppendByteString => 2

  | AndByteString
  | OrByteString
  | XorByteString  => 3
  | WriteBits => 3
  | ShiftByteString 
  | RotateByteString => 2
  | Ripemd_160 => 1
  | ReplicateByte => 2
  | ReadBit => 2
  | FindFirstSetBit => 1
  | ExpModInteger => 3
  | CountSetBits => 1
  | ComplementByteString => 1

  (* TODO: see Plutus Core Spec *)
  | _ => 1
  end
.
