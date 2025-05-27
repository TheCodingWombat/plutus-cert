{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Main where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
#if __GLASGOW_HASKELL__ >= 900
unsafeCoerce = GHC.Exts.unsafeCoerce#
#else
unsafeCoerce = GHC.Base.unsafeCoerce#
#endif
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rec :: a1
false_rec =
  Prelude.error "absurd case"

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r _ h _ =
  h

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f0 f1 l =
  case l of {
   ([]) -> f0;
   (:) y l0 -> f1 y l0 (list_rect f0 f1 l0)}

list_rec :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rec =
  list_rect

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

data SigT a p =
   ExistT a p

projT1 :: (SigT a1 a2) -> a1
projT1 x =
  case x of {
   ExistT a _ -> a}

sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f0 f1 s =
  case s of {
   Prelude.True -> f0 __;
   Prelude.False -> f1 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

data Uint =
   Nil
 | D0 Uint
 | D1 Uint
 | D2 Uint
 | D3 Uint
 | D4 Uint
 | D5 Uint
 | D6 Uint
 | D7 Uint
 | D8 Uint
 | D9 Uint

revapp :: Uint -> Uint -> Uint
revapp d d' =
  case d of {
   Nil -> d';
   D0 d0 -> revapp d0 (D0 d');
   D1 d0 -> revapp d0 (D1 d');
   D2 d0 -> revapp d0 (D2 d');
   D3 d0 -> revapp d0 (D3 d');
   D4 d0 -> revapp d0 (D4 d');
   D5 d0 -> revapp d0 (D5 d');
   D6 d0 -> revapp d0 (D6 d');
   D7 d0 -> revapp d0 (D7 d');
   D8 d0 -> revapp d0 (D8 d');
   D9 d0 -> revapp d0 (D9 d')}

rev :: Uint -> Uint
rev d =
  revapp d Nil

double :: Uint -> Uint
double d =
  case d of {
   Nil -> Nil;
   D0 d0 -> D0 (double d0);
   D1 d0 -> D2 (double d0);
   D2 d0 -> D4 (double d0);
   D3 d0 -> D6 (double d0);
   D4 d0 -> D8 (double d0);
   D5 d0 -> D0 (succ_double d0);
   D6 d0 -> D2 (succ_double d0);
   D7 d0 -> D4 (succ_double d0);
   D8 d0 -> D6 (succ_double d0);
   D9 d0 -> D8 (succ_double d0)}

succ_double :: Uint -> Uint
succ_double d =
  case d of {
   Nil -> D1 Nil;
   D0 d0 -> D1 (double d0);
   D1 d0 -> D3 (double d0);
   D2 d0 -> D5 (double d0);
   D3 d0 -> D7 (double d0);
   D4 d0 -> D9 (double d0);
   D5 d0 -> D1 (succ_double d0);
   D6 d0 -> D3 (succ_double d0);
   D7 d0 -> D5 (succ_double d0);
   D8 d0 -> D7 (succ_double d0);
   D9 d0 -> D9 (succ_double d0)}

to_little_uint :: Prelude.Integer -> Uint
to_little_uint p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> succ_double (to_little_uint p0))
    (\p0 -> double (to_little_uint p0))
    (\_ -> D1 Nil)
    p

to_uint :: Prelude.Integer -> Uint
to_uint p =
  rev (to_little_uint p)

in_dec :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (([]) a1) -> Prelude.Bool
in_dec h a l =
  list_rec Prelude.False (\a0 _ iHl ->
    let {s = h a0 a} in
    case s of {
     Prelude.True -> Prelude.True;
     Prelude.False -> iHl}) l

remove :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (([]) a1) -> ([]) a1
remove eq_dec x l =
  case l of {
   ([]) -> ([]);
   (:) y tl ->
    case eq_dec x y of {
     Prelude.True -> remove eq_dec x tl;
     Prelude.False -> (:) y (remove eq_dec x tl)}}

rev0 :: (([]) a1) -> ([]) a1
rev0 l =
  case l of {
   ([]) -> ([]);
   (:) x l' -> app (rev0 l') ((:) x ([]))}

concat :: (([]) (([]) a1)) -> ([]) a1
concat l =
  case l of {
   ([]) -> ([]);
   (:) x l0 -> app x (concat l0)}

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f0 l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f0 a) (map f0 t)}

fold_left :: (a1 -> a2 -> a1) -> (([]) a2) -> a1 -> a1
fold_left f0 l a0 =
  case l of {
   ([]) -> a0;
   (:) b t -> fold_left f0 t (f0 a0 b)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (([]) a2) -> a1
fold_right f0 a0 l =
  case l of {
   ([]) -> a0;
   (:) b t -> f0 b (fold_right f0 a0 t)}

existsb :: (a1 -> Prelude.Bool) -> (([]) a1) -> Prelude.Bool
existsb f0 l =
  case l of {
   ([]) -> Prelude.False;
   (:) a l0 -> (Prelude.||) (f0 a) (existsb f0 l0)}

forallb :: (a1 -> Prelude.Bool) -> (([]) a1) -> Prelude.Bool
forallb f0 l =
  case l of {
   ([]) -> Prelude.True;
   (:) a l0 -> (Prelude.&&) (f0 a) (forallb f0 l0)}

filter :: (a1 -> Prelude.Bool) -> (([]) a1) -> ([]) a1
filter f0 l =
  case l of {
   ([]) -> ([]);
   (:) x l0 ->
    case f0 x of {
     Prelude.True -> (:) x (filter f0 l0);
     Prelude.False -> filter f0 l0}}

find :: (a1 -> Prelude.Bool) -> (([]) a1) -> Prelude.Maybe a1
find f0 l =
  case l of {
   ([]) -> Prelude.Nothing;
   (:) x tl ->
    case f0 x of {
     Prelude.True -> Prelude.Just x;
     Prelude.False -> find f0 tl}}

append :: Prelude.String -> Prelude.String -> Prelude.String
append s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) c s1' -> (:) c (append s1' s2)}

concat0 :: Prelude.String -> (([]) Prelude.String) -> Prelude.String
concat0 sep ls =
  case ls of {
   ([]) -> "";
   (:) x xs ->
    case xs of {
     ([]) -> x;
     (:) _ _ -> append x (append sep (concat0 sep xs))}}

show_Z :: Prelude.Integer -> Prelude.String
show_Z = Prelude.show

ssr_have_upoly :: a1 -> (a1 -> a2) -> a2
ssr_have_upoly step rest =
  rest step

data ForallT a p =
   ForallT_nil
 | ForallT_cons a (([]) a) p (ForallT a p)

map2 :: (a1 -> a2) -> (([]) (([]) a1)) -> ([]) (([]) a2)
map2 f0 ll =
  map (map f0) ll

data ForallSet a p =
   ForallS_nil
 | ForallS_cons a (([]) a) p (ForallSet a p)

forallSet_rect :: a3 -> (a1 -> (([]) a1) -> a2 -> (ForallSet a1 a2) -> a3 ->
                  a3) -> (([]) a1) -> (ForallSet a1 a2) -> a3
forallSet_rect f0 f1 _ f2 =
  case f2 of {
   ForallS_nil -> f0;
   ForallS_cons x xs y f3 -> f1 x xs y f3 (forallSet_rect f0 f1 xs f3)}

forallSet_rec :: a3 -> (a1 -> (([]) a1) -> a2 -> (ForallSet a1 a2) -> a3 ->
                 a3) -> (([]) a1) -> (ForallSet a1 a2) -> a3
forallSet_rec =
  forallSet_rect

data ForallSet2 a p =
   ForallS2_nil
 | ForallS2_cons (([]) a) (([]) (([]) a)) (ForallSet a p) (ForallSet2 a p)

forallSet2_rect :: a3 -> ((([]) a1) -> (([]) (([]) a1)) -> (ForallSet 
                   a1 a2) -> (ForallSet2 a1 a2) -> a3 -> a3) -> (([])
                   (([]) a1)) -> (ForallSet2 a1 a2) -> a3
forallSet2_rect f0 f1 _ f2 =
  case f2 of {
   ForallS2_nil -> f0;
   ForallS2_cons x xs f3 f4 -> f1 x xs f3 f4 (forallSet2_rect f0 f1 xs f4)}

forallSet2_rec :: a3 -> ((([]) a1) -> (([]) (([]) a1)) -> (ForallSet 
                  a1 a2) -> (ForallSet2 a1 a2) -> a3 -> a3) -> (([])
                  (([]) a1)) -> (ForallSet2 a1 a2) -> a3
forallSet2_rec =
  forallSet2_rect

flatmap2 :: (a1 -> ([]) a2) -> (([]) (([]) a1)) -> ([]) a2
flatmap2 f0 l =
  fold_right (\ts acc ->
    app (fold_right (\t acc2 -> app (f0 t) acc2) ([]) ts) acc) ([]) l

bind :: (Prelude.Maybe a1) -> (a1 -> Prelude.Maybe a2) -> Prelude.Maybe a2
bind xx f0 =
  case xx of {
   Prelude.Just a -> f0 a;
   Prelude.Nothing -> Prelude.Nothing}

inb_string :: Prelude.String -> (([]) Prelude.String) -> Prelude.Bool
inb_string x xs =
  case in_dec
         ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
         xs of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

data Recursivity =
   NonRec
 | Rec
 deriving (Prelude.Show)

data Strictness =
   NonStrict
 | Strict
 deriving (Prelude.Show)

data DefaultUni =
   DefaultUniInteger
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
 | DefaultUniApply DefaultUni DefaultUni
 deriving (Prelude.Show)

defaultUni_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1
                   -> a1 -> (DefaultUni -> a1 -> DefaultUni -> a1 -> a1) ->
                   DefaultUni -> a1
defaultUni_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 d =
  case d of {
   DefaultUniInteger -> f0;
   DefaultUniByteString -> f1;
   DefaultUniString -> f2;
   DefaultUniUnit -> f3;
   DefaultUniBool -> f4;
   DefaultUniProtoList -> f5;
   DefaultUniProtoPair -> f6;
   DefaultUniData -> f7;
   DefaultUniBLS12_381_G1_Element -> f8;
   DefaultUniBLS12_381_G2_Element -> f9;
   DefaultUniBLS12_381_MlResult -> f10;
   DefaultUniApply d0 d1 ->
    f11 d0 (defaultUni_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 d0) d1
      (defaultUni_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 d1)}

defaultUni_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
                  a1 -> (DefaultUni -> a1 -> DefaultUni -> a1 -> a1) ->
                  DefaultUni -> a1
defaultUni_rec =
  defaultUni_rect

type UniType = Any

data Constant =
   ValueOf DefaultUni UniType

data DefaultFun =
   AddInteger
 | SubtractInteger
 | MultiplyInteger
 | DivideInteger
 | QuotientInteger
 | RemainderInteger
 | ModInteger
 | EqualsInteger
 | LessThanInteger
 | LessThanEqualsInteger
 | AppendByteString
 | ConsByteString
 | SliceByteString
 | LengthOfByteString
 | IndexByteString
 | EqualsByteString
 | LessThanByteString
 | LessThanEqualsByteString
 | Sha2_256
 | Sha3_256
 | Blake2b_256
 | VerifyEd25519Signature
 | VerifyEcdsaSecp256k1Signature
 | VerifySchnorrSecp256k1Signature
 | AppendString
 | EqualsString
 | EncodeUtf8
 | DecodeUtf8
 | IfThenElse
 | ChooseUnit
 | Trace
 | FstPair
 | SndPair
 | ChooseList
 | MkCons
 | HeadList
 | TailList
 | NullList
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
 | MkPairData
 | MkNilData
 | MkNilPairData
 | Bls12_381_G1_add
 | Bls12_381_G1_neg
 | Bls12_381_G1_scalarMul
 | Bls12_381_G1_equal
 | Bls12_381_G1_hashToGroup
 | Bls12_381_G1_compress
 | Bls12_381_G1_uncompress
 | Bls12_381_G2_add
 | Bls12_381_G2_neg
 | Bls12_381_G2_scalarMul
 | Bls12_381_G2_equal
 | Bls12_381_G2_hashToGroup
 | Bls12_381_G2_compress
 | Bls12_381_G2_uncompress
 | Bls12_381_millerLoop
 | Bls12_381_mulMlResult
 | Bls12_381_finalVerify
 | Keccak_256
 | Blake2b_224
 | IntegerToByteString
 | ByteStringToInteger
 | XorByteString
 | WriteBits
 | ShiftByteString
 | RotateByteString
 | Ripemd_160
 | ReplicateByte
 | ReadBit
 | OrByteString
 | FindFirstSetBit
 | ExpModInteger
 | CountSetBits
 | ComplementByteString
 | AndByteString
 deriving (Prelude.Show)

type Name = Prelude.String

type Tyname = Prelude.String

type BinderName = Prelude.String

type BinderTyname = Prelude.String

data Kind =
   Kind_Base
 | Kind_Arrow Kind Kind
 deriving (Prelude.Show)

kind_rect :: a1 -> (Kind -> a1 -> Kind -> a1 -> a1) -> Kind -> a1
kind_rect f0 f1 k =
  case k of {
   Kind_Base -> f0;
   Kind_Arrow k0 k1 -> f1 k0 (kind_rect f0 f1 k0) k1 (kind_rect f0 f1 k1)}

kind_rec :: a1 -> (Kind -> a1 -> Kind -> a1 -> a1) -> Kind -> a1
kind_rec =
  kind_rect

data Ty =
   Ty_Var Tyname
 | Ty_Fun Ty Ty
 | Ty_IFix Ty Ty
 | Ty_Forall BinderTyname Kind Ty
 | Ty_Builtin DefaultUni
 | Ty_Lam BinderTyname Kind Ty
 | Ty_App Ty Ty
 | Ty_SOP (([]) (([]) Ty))
 deriving (Prelude.Show)

ty_rect :: (Tyname -> a1) -> (Ty -> a1 -> Ty -> a1 -> a1) -> (Ty -> a1 -> Ty
           -> a1 -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
           (DefaultUni -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
           (Ty -> a1 -> Ty -> a1 -> a1) -> ((([]) (([]) Ty)) -> a1) -> Ty ->
           a1
ty_rect f0 f1 f2 f3 f4 f5 f6 f7 t =
  case t of {
   Ty_Var t0 -> f0 t0;
   Ty_Fun t0 t1 ->
    f1 t0 (ty_rect f0 f1 f2 f3 f4 f5 f6 f7 t0) t1
      (ty_rect f0 f1 f2 f3 f4 f5 f6 f7 t1);
   Ty_IFix t0 t1 ->
    f2 t0 (ty_rect f0 f1 f2 f3 f4 f5 f6 f7 t0) t1
      (ty_rect f0 f1 f2 f3 f4 f5 f6 f7 t1);
   Ty_Forall b k t0 -> f3 b k t0 (ty_rect f0 f1 f2 f3 f4 f5 f6 f7 t0);
   Ty_Builtin d -> f4 d;
   Ty_Lam b k t0 -> f5 b k t0 (ty_rect f0 f1 f2 f3 f4 f5 f6 f7 t0);
   Ty_App t0 t1 ->
    f6 t0 (ty_rect f0 f1 f2 f3 f4 f5 f6 f7 t0) t1
      (ty_rect f0 f1 f2 f3 f4 f5 f6 f7 t1);
   Ty_SOP l -> f7 l}

ty_rec :: (Tyname -> a1) -> (Ty -> a1 -> Ty -> a1 -> a1) -> (Ty -> a1 -> Ty
          -> a1 -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
          (DefaultUni -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
          (Ty -> a1 -> Ty -> a1 -> a1) -> ((([]) (([]) Ty)) -> a1) -> Ty ->
          a1
ty_rec =
  ty_rect

data Vdecl =
   VarDecl BinderName Ty

data Tvdecl =
   TyVarDecl BinderTyname Kind

data Dtdecl =
   Datatype Tvdecl (([]) Tvdecl) BinderName (([]) Vdecl)

data Term =
   Let Recursivity (([]) Binding) Term
 | Var Name
 | TyAbs BinderTyname Kind Term
 | LamAbs BinderName Ty Term
 | Apply Term Term
 | Constant0 Constant
 | Builtin DefaultFun
 | TyInst Term Ty
 | Error Ty
 | IWrap Ty Ty Term
 | Unwrap Term
 | Constr Ty Uint (([]) Term)
 | Case Ty Term (([]) Term)
data Binding =
   TermBind Strictness Vdecl Term
 | TypeBind Tvdecl Ty
 | DatatypeBind Dtdecl

vdecl_name :: Vdecl -> BinderName
vdecl_name c =
  case c of {
   VarDecl n _ -> n}

vdecl_ty :: Vdecl -> Ty
vdecl_ty c =
  case c of {
   VarDecl _ ty -> ty}

tvdecl_name :: Tvdecl -> BinderTyname
tvdecl_name tvd =
  case tvd of {
   TyVarDecl v _ -> v}

splitTy :: Ty -> (,) (([]) Ty) Ty
splitTy t =
  case t of {
   Ty_Fun targ t' -> (,) ((:) targ (fst (splitTy t'))) (snd (splitTy t'));
   _ -> (,) ([]) t}

lookup :: Prelude.String -> (([]) ((,) Prelude.String a1)) -> Prelude.Maybe
          a1
lookup k l =
  case l of {
   ([]) -> Prelude.Nothing;
   (:) p l' ->
    case p of {
     (,) j x ->
      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             j k of {
       Prelude.True -> Prelude.Just x;
       Prelude.False -> lookup k l'}}}

type EqDec a = a -> a -> Prelude.Bool

defaultUni_dec :: EqDec DefaultUni
defaultUni_dec x y =
  defaultUni_rec (\x0 ->
    case x0 of {
     DefaultUniInteger -> Prelude.True;
     _ -> Prelude.False}) (\x0 ->
    case x0 of {
     DefaultUniByteString -> Prelude.True;
     _ -> Prelude.False}) (\x0 ->
    case x0 of {
     DefaultUniString -> Prelude.True;
     _ -> Prelude.False}) (\x0 ->
    case x0 of {
     DefaultUniUnit -> Prelude.True;
     _ -> Prelude.False}) (\x0 ->
    case x0 of {
     DefaultUniBool -> Prelude.True;
     _ -> Prelude.False}) (\x0 ->
    case x0 of {
     DefaultUniProtoList -> Prelude.True;
     _ -> Prelude.False}) (\x0 ->
    case x0 of {
     DefaultUniProtoPair -> Prelude.True;
     _ -> Prelude.False}) (\x0 ->
    case x0 of {
     DefaultUniData -> Prelude.True;
     _ -> Prelude.False}) (\x0 ->
    case x0 of {
     DefaultUniBLS12_381_G1_Element -> Prelude.True;
     _ -> Prelude.False}) (\x0 ->
    case x0 of {
     DefaultUniBLS12_381_G2_Element -> Prelude.True;
     _ -> Prelude.False}) (\x0 ->
    case x0 of {
     DefaultUniBLS12_381_MlResult -> Prelude.True;
     _ -> Prelude.False}) (\_ x0 _ x1 x2 ->
    case x2 of {
     DefaultUniApply d d0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (x1 d0))
        (\_ -> Prelude.False) (x0 d);
     _ -> Prelude.False}) x y

kind_dec :: EqDec Kind
kind_dec x y =
  kind_rec (\x0 ->
    case x0 of {
     Kind_Base -> Prelude.True;
     Kind_Arrow _ _ -> Prelude.False}) (\_ x0 _ x1 x2 ->
    case x2 of {
     Kind_Base -> Prelude.False;
     Kind_Arrow k k0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (x1 k0))
        (\_ -> Prelude.False) (x0 k)}) x y

list_Ty_dec_axiom :: (([]) (([]) Ty)) -> (([]) (([]) Ty)) -> Prelude.Bool
list_Ty_dec_axiom =
  Prelude.error "AXIOM TO BE REALIZED (PlutusCert.PlutusIR.Analysis.Equality.list_Ty_dec_axiom)"

ty_dec :: EqDec Ty
ty_dec x y =
  ty_rec (\t x0 ->
    case x0 of {
     Ty_Var t0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
        (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) t
          t0);
     _ -> Prelude.False}) (\_ x0 _ x1 x2 ->
    case x2 of {
     Ty_Fun t t0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (x1 t0))
        (\_ -> Prelude.False) (x0 t);
     _ -> Prelude.False}) (\_ x0 _ x1 x2 ->
    case x2 of {
     Ty_IFix t t0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (x1 t0))
        (\_ -> Prelude.False) (x0 t);
     _ -> Prelude.False}) (\b k _ x0 x1 ->
    case x1 of {
     Ty_Forall b0 k0 t ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (x0 t))
          (\_ -> Prelude.False) (kind_dec k k0)) (\_ -> Prelude.False)
        (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) b
          b0);
     _ -> Prelude.False}) (\d x0 ->
    case x0 of {
     Ty_Builtin d0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
        (defaultUni_dec d d0);
     _ -> Prelude.False}) (\b k _ x0 x1 ->
    case x1 of {
     Ty_Lam b0 k0 t ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (x0 t))
          (\_ -> Prelude.False) (kind_dec k k0)) (\_ -> Prelude.False)
        (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) b
          b0);
     _ -> Prelude.False}) (\_ x0 _ x1 x2 ->
    case x2 of {
     Ty_App t t0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (x1 t0))
        (\_ -> Prelude.False) (x0 t);
     _ -> Prelude.False}) (\l x0 ->
    case x0 of {
     Ty_SOP l0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
        (list_Ty_dec_axiom l l0);
     _ -> Prelude.False}) x y

type Eqb x = x -> x -> Prelude.Bool

eq_dec_to_eqb :: (EqDec a1) -> Eqb a1
eq_dec_to_eqb dec_eq x y =
  case dec_eq x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

kind_eqb :: Eqb Kind
kind_eqb =
  eq_dec_to_eqb kind_dec

ty_eqb :: Eqb Ty
ty_eqb =
  eq_dec_to_eqb ty_dec

some :: a1 -> a1
some x =
  x

substituteT :: Prelude.String -> Ty -> Ty -> Ty
substituteT x u t =
  case t of {
   Ty_Var y ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
           y of {
     Prelude.True -> u;
     Prelude.False -> Ty_Var y};
   Ty_Fun t1 t2 -> Ty_Fun (substituteT x u t1) (substituteT x u t2);
   Ty_IFix f0 t0 -> Ty_IFix (substituteT x u f0) (substituteT x u t0);
   Ty_Forall y k t' ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
           y of {
     Prelude.True -> Ty_Forall y k t';
     Prelude.False -> Ty_Forall y k (substituteT x u t')};
   Ty_Builtin u0 -> Ty_Builtin u0;
   Ty_Lam y k1 t' ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
           y of {
     Prelude.True -> Ty_Lam y k1 t';
     Prelude.False -> Ty_Lam y k1 (substituteT x u t')};
   Ty_App t1 t2 -> Ty_App (substituteT x u t1) (substituteT x u t2);
   Ty_SOP tss -> Ty_SOP (map2 (substituteT x u) tss)}

ftv :: Ty -> ([]) Prelude.String
ftv t =
  case t of {
   Ty_Var x -> (:) x ([]);
   Ty_Fun t1 t2 -> app (ftv t1) (ftv t2);
   Ty_IFix f0 t0 -> app (ftv f0) (ftv t0);
   Ty_Forall x _ t' ->
    remove ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
      x (ftv t');
   Ty_Builtin _ -> ([]);
   Ty_Lam x _ t' ->
    remove ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
      x (ftv t');
   Ty_App t1 t2 -> app (ftv t1) (ftv t2);
   Ty_SOP tss -> flatmap2 ftv tss}

plutusTv :: Ty -> ([]) Prelude.String
plutusTv t =
  case t of {
   Ty_Var x -> (:) x ([]);
   Ty_Fun t1 t2 -> app (plutusTv t1) (plutusTv t2);
   Ty_IFix f1 t1 -> app (plutusTv f1) (plutusTv t1);
   Ty_Forall x _ t0 -> (:) x (plutusTv t0);
   Ty_Builtin _ -> ([]);
   Ty_Lam x _ t0 -> (:) x (plutusTv t0);
   Ty_App t1 t2 -> app (plutusTv t1) (plutusTv t2);
   Ty_SOP tss -> flatmap2 plutusTv tss}

fresh :: Prelude.String -> Ty -> Ty -> Prelude.String
fresh x u t =
  append "a"
    (append x (append (concat0 "" (plutusTv u)) (concat0 "" (plutusTv t))))

rename :: Prelude.String -> Prelude.String -> Ty -> Ty
rename x y t =
  substituteT x (Ty_Var y) t

map' :: (([]) a1) -> (a1 -> () -> a2) -> ([]) a2
map' xs x =
  case xs of {
   ([]) -> ([]);
   (:) x0 xs0 -> (:) (x x0 __) (map' xs0 (\y _ -> x y __))}

substituteTCA :: Prelude.String -> Ty -> Ty -> Ty
substituteTCA a a0 b =
  let {
   fix_F x =
     let {x0 = case x of {
                (,) pr1 _ -> pr1}} in
     let {u = case case x of {
                    (,) _ pr2 -> pr2} of {
               (,) pr1 _ -> pr1}} in
     let {
      substituteTCA1 = \a1 a2 b0 ->
       let {y = (,) a1 ((,) a2 b0)} in (\_ -> fix_F y)}
     in
     case case case x of {
                (,) _ pr2 -> pr2} of {
           (,) _ pr2 -> pr2} of {
      Ty_Var t ->
       case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
              x0 t of {
        Prelude.True -> u;
        Prelude.False -> Ty_Var t};
      Ty_Fun t t0 -> Ty_Fun (substituteTCA1 x0 u t __)
       (substituteTCA1 x0 u t0 __);
      Ty_IFix t t0 -> Ty_IFix (substituteTCA1 x0 u t __)
       (substituteTCA1 x0 u t0 __);
      Ty_Forall b0 k t ->
       case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
              x0 b0 of {
        Prelude.True -> Ty_Forall b0 k t;
        Prelude.False ->
         case existsb
                (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                  b0) (ftv u) of {
          Prelude.True ->
           let {y' = fresh x0 u t} in
           let {t' = rename b0 y' t} in
           Ty_Forall y' k (substituteTCA1 x0 u t' __);
          Prelude.False -> Ty_Forall b0 k (substituteTCA1 x0 u t __)}};
      Ty_Builtin d -> Ty_Builtin d;
      Ty_Lam b0 k t ->
       case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
              x0 b0 of {
        Prelude.True -> Ty_Lam b0 k t;
        Prelude.False ->
         case existsb
                (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                  b0) (ftv u) of {
          Prelude.True ->
           let {y' = fresh x0 u t} in
           let {t' = rename b0 y' t} in
           Ty_Lam y' k (substituteTCA1 x0 u t' __);
          Prelude.False -> Ty_Lam b0 k (substituteTCA1 x0 u t __)}};
      Ty_App t t0 -> Ty_App (substituteTCA1 x0 u t __)
       (substituteTCA1 x0 u t0 __);
      Ty_SOP l -> Ty_SOP
       (map' l (\ts _ -> map' ts (\t _ -> substituteTCA1 x0 u t __)))}}
  in fix_F ((,) a ((,) a0 b))

data Has_kind_set =
   K_Var_set (([]) ((,) Prelude.String Kind)) Prelude.String Kind
 | K_Fun_set (([]) ((,) BinderTyname Kind)) Ty Ty Has_kind_set Has_kind_set
 | K_IFix_set (([]) ((,) BinderTyname Kind)) Ty Ty Kind Has_kind_set 
 Has_kind_set
 | K_Forall_set (([]) ((,) BinderTyname Kind)) BinderTyname Kind Ty Has_kind_set
 | K_Builtin_set (([]) ((,) BinderTyname Kind)) DefaultUni
 | K_Lam_set (([]) ((,) BinderTyname Kind)) BinderTyname Kind Ty Kind 
 Has_kind_set
 | K_App_set (([]) ((,) BinderTyname Kind)) Ty Ty Kind Kind Has_kind_set 
 Has_kind_set
 | K_SOP_set (([]) ((,) BinderTyname Kind)) (([]) (([]) Ty)) (ForallT
                                                             (([]) Ty)
                                                             (ForallT 
                                                             Ty Has_kind_set))

has_kind_set__ind :: ((([]) ((,) Prelude.String Kind)) -> Prelude.String ->
                     Kind -> () -> a1) -> ((([]) ((,) BinderTyname Kind)) ->
                     Ty -> Ty -> a1 -> a1 -> a1) -> ((([])
                     ((,) BinderTyname Kind)) -> Ty -> Ty -> Kind -> a1 -> a1
                     -> a1) -> ((([]) ((,) BinderTyname Kind)) ->
                     BinderTyname -> Kind -> Ty -> a1 -> a1) -> ((([])
                     ((,) BinderTyname Kind)) -> DefaultUni -> () -> a1) ->
                     ((([]) ((,) BinderTyname Kind)) -> BinderTyname -> Kind
                     -> Ty -> Kind -> a1 -> a1) -> ((([])
                     ((,) BinderTyname Kind)) -> Ty -> Ty -> Kind -> Kind ->
                     a1 -> a1 -> a1) -> ((([]) ((,) BinderTyname Kind)) ->
                     (([]) (([]) Ty)) -> (ForallT (([]) Ty) (ForallT Ty a1))
                     -> a1) -> (([]) ((,) BinderTyname Kind)) -> Ty -> Kind
                     -> Has_kind_set -> a1
has_kind_set__ind h_Var_set h_Fun_set h_IFix_set h_Forall_set h_Builtin_set h_Lam_set h_App_set h_SOP_set _ _ _ hK =
  case hK of {
   K_Var_set _UU0394_ x k -> h_Var_set _UU0394_ x k __;
   K_Fun_set _UU0394_ t1 t2 hK1 hK2 ->
    h_Fun_set _UU0394_ t1 t2
      (has_kind_set__ind h_Var_set h_Fun_set h_IFix_set h_Forall_set
        h_Builtin_set h_Lam_set h_App_set h_SOP_set _UU0394_ t1 Kind_Base
        hK1)
      (has_kind_set__ind h_Var_set h_Fun_set h_IFix_set h_Forall_set
        h_Builtin_set h_Lam_set h_App_set h_SOP_set _UU0394_ t2 Kind_Base
        hK2);
   K_IFix_set _UU0394_ f0 t k hKT hKF ->
    h_IFix_set _UU0394_ f0 t k
      (has_kind_set__ind h_Var_set h_Fun_set h_IFix_set h_Forall_set
        h_Builtin_set h_Lam_set h_App_set h_SOP_set _UU0394_ t k hKT)
      (has_kind_set__ind h_Var_set h_Fun_set h_IFix_set h_Forall_set
        h_Builtin_set h_Lam_set h_App_set h_SOP_set _UU0394_ f0 (Kind_Arrow
        (Kind_Arrow k Kind_Base) (Kind_Arrow k Kind_Base)) hKF);
   K_Forall_set _UU0394_ x k t hKT ->
    h_Forall_set _UU0394_ x k t
      (has_kind_set__ind h_Var_set h_Fun_set h_IFix_set h_Forall_set
        h_Builtin_set h_Lam_set h_App_set h_SOP_set ((:) ((,) x k) _UU0394_)
        t Kind_Base hKT);
   K_Builtin_set _UU0394_ t -> h_Builtin_set _UU0394_ t __;
   K_Lam_set _UU0394_ x k1 t k2 hKT ->
    h_Lam_set _UU0394_ x k1 t k2
      (has_kind_set__ind h_Var_set h_Fun_set h_IFix_set h_Forall_set
        h_Builtin_set h_Lam_set h_App_set h_SOP_set ((:) ((,) x k1) _UU0394_)
        t k2 hKT);
   K_App_set _UU0394_ t1 t2 k1 k2 hK1 hK2 ->
    h_App_set _UU0394_ t1 t2 k1 k2
      (has_kind_set__ind h_Var_set h_Fun_set h_IFix_set h_Forall_set
        h_Builtin_set h_Lam_set h_App_set h_SOP_set _UU0394_ t1 (Kind_Arrow
        k1 k2) hK1)
      (has_kind_set__ind h_Var_set h_Fun_set h_IFix_set h_Forall_set
        h_Builtin_set h_Lam_set h_App_set h_SOP_set _UU0394_ t2 k1 hK2);
   K_SOP_set _UU0394_ tss hForallT ->
    h_SOP_set _UU0394_ tss
      (let {
        map_outer _ h =
          case h of {
           ForallT_nil -> ForallT_nil;
           ForallT_cons x l hts hrest ->
            let {
             map_inner = let {
                          map_inner _ hts0 =
                            case hts0 of {
                             ForallT_nil -> ForallT_nil;
                             ForallT_cons x0 l0 ht hts' -> ForallT_cons x0 l0
                              (has_kind_set__ind h_Var_set h_Fun_set
                                h_IFix_set h_Forall_set h_Builtin_set
                                h_Lam_set h_App_set h_SOP_set _UU0394_ x0
                                Kind_Base ht) (map_inner l0 hts')}}
                         in map_inner}
            in
            ForallT_cons x l (map_inner x hts) (map_outer l hrest)}}
       in map_outer tss hForallT)}

kind_check_default_uni :: DefaultUni -> Prelude.Maybe Kind
kind_check_default_uni d =
  case d of {
   DefaultUniProtoList -> Prelude.Just (Kind_Arrow Kind_Base Kind_Base);
   DefaultUniProtoPair -> Prelude.Just (Kind_Arrow Kind_Base (Kind_Arrow
    Kind_Base Kind_Base));
   DefaultUniApply t t' ->
    let {o = kind_check_default_uni t} in
    let {o0 = kind_check_default_uni t'} in
    case o of {
     Prelude.Just k0 ->
      case k0 of {
       Kind_Base -> Prelude.Nothing;
       Kind_Arrow k k' ->
        case o0 of {
         Prelude.Just k'' ->
          case kind_eqb k'' k of {
           Prelude.True -> Prelude.Just k';
           Prelude.False -> Prelude.Nothing};
         Prelude.Nothing -> Prelude.Nothing}};
     Prelude.Nothing -> Prelude.Nothing};
   _ -> Prelude.Just Kind_Base}

kind_check :: (([]) ((,) BinderTyname Kind)) -> Ty -> Prelude.Maybe Kind
kind_check delta ty =
  case ty of {
   Ty_Var x -> lookup x delta;
   Ty_Fun t1 t2 ->
    let {o = kind_check delta t1} in
    let {o0 = kind_check delta t2} in
    case o of {
     Prelude.Just k ->
      case k of {
       Kind_Base ->
        case o0 of {
         Prelude.Just k0 ->
          case k0 of {
           Kind_Base -> Prelude.Just Kind_Base;
           Kind_Arrow _ _ -> Prelude.Nothing};
         Prelude.Nothing -> Prelude.Nothing};
       Kind_Arrow _ _ -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   Ty_IFix f0 t ->
    case kind_check delta t of {
     Prelude.Just k ->
      case kind_check delta f0 of {
       Prelude.Just k0 ->
        case k0 of {
         Kind_Base -> Prelude.Nothing;
         Kind_Arrow k1 k2 ->
          case k1 of {
           Kind_Base -> Prelude.Nothing;
           Kind_Arrow k3 k4 ->
            case k4 of {
             Kind_Base ->
              case k2 of {
               Kind_Base -> Prelude.Nothing;
               Kind_Arrow k5 k6 ->
                case k6 of {
                 Kind_Base ->
                  case (Prelude.&&) (kind_eqb k k3) (kind_eqb k k5) of {
                   Prelude.True -> Prelude.Just Kind_Base;
                   Prelude.False -> Prelude.Nothing};
                 Kind_Arrow _ _ -> Prelude.Nothing}};
             Kind_Arrow _ _ -> Prelude.Nothing}}};
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   Ty_Forall x k t ->
    case kind_check ((:) ((,) x k) delta) t of {
     Prelude.Just k0 ->
      case k0 of {
       Kind_Base -> Prelude.Just Kind_Base;
       Kind_Arrow _ _ -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   Ty_Builtin d ->
    case kind_check_default_uni d of {
     Prelude.Just k ->
      case k of {
       Kind_Base -> Prelude.Just Kind_Base;
       Kind_Arrow _ _ -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   Ty_Lam x k1 t ->
    case kind_check ((:) ((,) x k1) delta) t of {
     Prelude.Just k2 -> Prelude.Just (Kind_Arrow k1 k2);
     Prelude.Nothing -> Prelude.Nothing};
   Ty_App t1 t2 ->
    let {o = kind_check delta t1} in
    let {o0 = kind_check delta t2} in
    case o of {
     Prelude.Just k ->
      case k of {
       Kind_Base -> Prelude.Nothing;
       Kind_Arrow k11 k2 ->
        case o0 of {
         Prelude.Just k12 ->
          case kind_eqb k11 k12 of {
           Prelude.True -> Prelude.Just k2;
           Prelude.False -> Prelude.Nothing};
         Prelude.Nothing -> Prelude.Nothing}};
     Prelude.Nothing -> Prelude.Nothing};
   Ty_SOP tss ->
    case forallb (\ts ->
           forallb (\t ->
             case kind_check delta t of {
              Prelude.Just k ->
               case k of {
                Kind_Base -> Prelude.True;
                Kind_Arrow _ _ -> Prelude.False};
              Prelude.Nothing -> Prelude.False}) ts) tss of {
     Prelude.True -> Prelude.Just Kind_Base;
     Prelude.False -> Prelude.Nothing}}

ty__ind_set :: (Tyname -> a1) -> (Ty -> Ty -> a1 -> a1 -> a1) -> (Ty -> Ty ->
               a1 -> a1 -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
               (DefaultUni -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1)
               -> (Ty -> Ty -> a1 -> a1 -> a1) -> ((([]) (([]) Ty)) ->
               (ForallT (([]) Ty) (ForallT Ty a1)) -> a1) -> Ty -> a1
ty__ind_set h_Var h_Fun h_IFix h_Forall h_Builtin h_Lam h_App h_SOP t =
  case t of {
   Ty_Var x -> h_Var x;
   Ty_Fun t1 t2 ->
    h_Fun t1 t2
      (ty__ind_set h_Var h_Fun h_IFix h_Forall h_Builtin h_Lam h_App h_SOP
        t1)
      (ty__ind_set h_Var h_Fun h_IFix h_Forall h_Builtin h_Lam h_App h_SOP
        t2);
   Ty_IFix f0 t0 ->
    h_IFix f0 t0
      (ty__ind_set h_Var h_Fun h_IFix h_Forall h_Builtin h_Lam h_App h_SOP
        f0)
      (ty__ind_set h_Var h_Fun h_IFix h_Forall h_Builtin h_Lam h_App h_SOP
        t0);
   Ty_Forall x k t0 ->
    h_Forall x k t0
      (ty__ind_set h_Var h_Fun h_IFix h_Forall h_Builtin h_Lam h_App h_SOP
        t0);
   Ty_Builtin t0 -> h_Builtin t0;
   Ty_Lam x k t0 ->
    h_Lam x k t0
      (ty__ind_set h_Var h_Fun h_IFix h_Forall h_Builtin h_Lam h_App h_SOP
        t0);
   Ty_App t1 t2 ->
    h_App t1 t2
      (ty__ind_set h_Var h_Fun h_IFix h_Forall h_Builtin h_Lam h_App h_SOP
        t1)
      (ty__ind_set h_Var h_Fun h_IFix h_Forall h_Builtin h_Lam h_App h_SOP
        t2);
   Ty_SOP tss ->
    h_SOP tss
      (let {
        list_list_ind tss0 =
          case tss0 of {
           ([]) -> ForallT_nil;
           (:) ts tss' -> ForallT_cons ts tss'
            (let {
              list_ind ts0 =
                case ts0 of {
                 ([]) -> ForallT_nil;
                 (:) t0 ts' -> ForallT_cons t0 ts'
                  (ty__ind_set h_Var h_Fun h_IFix h_Forall h_Builtin h_Lam
                    h_App h_SOP t0) (list_ind ts')}}
             in list_ind ts) (list_list_ind tss')}}
       in list_list_ind tss)}

kind_checking_sound_set_TySOP :: (([]) Ty) -> (([]) (([]) Ty)) -> (([])
                                 ((,) BinderTyname Kind)) -> ForallT
                                 (([]) Ty) (ForallT Ty Has_kind_set)
kind_checking_sound_set_TySOP =
  Prelude.error "AXIOM TO BE REALIZED (PlutusCert.PlutusIR.Semantics.Static.Kinding.Checker.kind_checking_sound_set_TySOP)"

kind_checking_sound_set :: (([]) ((,) BinderTyname Kind)) -> Ty -> Kind ->
                           Has_kind_set
kind_checking_sound_set delta ty kind =
  ty__ind_set (\x delta0 kind0 _ -> K_Var_set delta0 x kind0)
    (\ty1 ty2 iHty1 iHty2 delta0 _ _ ->
    let {o = kind_check delta0 ty1} in
    case o of {
     Prelude.Just k ->
      case k of {
       Kind_Base ->
        let {o0 = kind_check delta0 ty2} in
        case o0 of {
         Prelude.Just k0 ->
          case k0 of {
           Kind_Base -> K_Fun_set delta0 ty1 ty2 (iHty1 delta0 Kind_Base __)
            (iHty2 delta0 Kind_Base __);
           Kind_Arrow _ _ -> false_rec};
         Prelude.Nothing -> false_rec};
       Kind_Arrow _ _ -> false_rec};
     Prelude.Nothing -> false_rec}) (\ty1 ty2 iHty1 iHty2 delta0 _ _ ->
    let {o = kind_check delta0 ty2} in
    case o of {
     Prelude.Just k ->
      let {o0 = kind_check delta0 ty1} in
      case o0 of {
       Prelude.Just k0 ->
        case k0 of {
         Kind_Base -> false_rec;
         Kind_Arrow k1 k2 ->
          case k1 of {
           Kind_Base -> false_rec;
           Kind_Arrow k3 k4 ->
            case k4 of {
             Kind_Base ->
              case k2 of {
               Kind_Base -> false_rec;
               Kind_Arrow k5 k6 ->
                case k6 of {
                 Kind_Base ->
                  let {b = (Prelude.&&) (kind_eqb k k3) (kind_eqb k k5)} in
                  case b of {
                   Prelude.True -> K_IFix_set delta0 ty1 ty2 k
                    (iHty2 delta0 k __)
                    (iHty1 delta0 (Kind_Arrow (Kind_Arrow k Kind_Base)
                      (Kind_Arrow k Kind_Base)) __);
                   Prelude.False -> false_rec};
                 Kind_Arrow _ _ -> false_rec}};
             Kind_Arrow _ _ -> false_rec}}};
       Prelude.Nothing -> false_rec};
     Prelude.Nothing -> false_rec}) (\x k ty0 iHty delta0 _ _ ->
    let {o = kind_check ((:) ((,) x k) delta0) ty0} in
    case o of {
     Prelude.Just k0 ->
      case k0 of {
       Kind_Base -> K_Forall_set delta0 x k ty0
        (iHty ((:) ((,) x k) delta0) Kind_Base __);
       Kind_Arrow _ _ -> false_rec};
     Prelude.Nothing -> false_rec}) (\t delta0 _ _ ->
    let {o = kind_check_default_uni t} in
    case o of {
     Prelude.Just k ->
      case k of {
       Kind_Base -> K_Builtin_set delta0 t;
       Kind_Arrow _ _ -> false_rec};
     Prelude.Nothing -> false_rec}) (\x k ty0 iHty delta0 _ _ ->
    let {o = kind_check ((:) ((,) x k) delta0) ty0} in
    case o of {
     Prelude.Just k0 -> K_Lam_set delta0 x k ty0 k0
      (iHty ((:) ((,) x k) delta0) k0 __);
     Prelude.Nothing -> false_rec}) (\ty1 ty2 iHty1 iHty2 delta0 kind0 _ ->
    let {k1 = kind_check delta0 ty2} in
    case k1 of {
     Prelude.Just k ->
      let {o = kind_check delta0 ty1} in
      case o of {
       Prelude.Just k0 ->
        case k0 of {
         Kind_Base -> false_rec;
         Kind_Arrow k2 _ ->
          let {b = kind_eqb k2 k} in
          case b of {
           Prelude.True -> K_App_set delta0 ty1 ty2 k kind0
            (iHty1 delta0 (Kind_Arrow k kind0) __) (iHty2 delta0 k __);
           Prelude.False -> false_rec}};
       Prelude.Nothing -> false_rec};
     Prelude.Nothing -> false_rec}) (\tss h delta0 _ _ ->
    let {
     b = forallb (\ts ->
           forallb (\t ->
             case kind_check delta0 t of {
              Prelude.Just k ->
               case k of {
                Kind_Base -> Prelude.True;
                Kind_Arrow _ _ -> Prelude.False};
              Prelude.Nothing -> Prelude.False}) ts) tss}
    in
    case b of {
     Prelude.True -> K_SOP_set delta0 tss
      (case h of {
        ForallT_nil -> ForallT_nil;
        ForallT_cons x l _ _ -> kind_checking_sound_set_TySOP x l delta0});
     Prelude.False -> false_rec}) ty delta kind __

prop_to_type :: (([]) ((,) BinderTyname Kind)) -> Ty -> Kind -> Has_kind_set
prop_to_type =
  kind_checking_sound_set

data Step =
   Step_beta Prelude.String Kind Ty Ty
 | Step_appL Ty Ty Ty Step
 | Step_appR Ty Ty Ty Step
 | Step_funL Ty Ty Ty Step
 | Step_funR Ty Ty Ty Step
 | Step_forall BinderTyname Kind Ty Ty Step
 | Step_abs BinderTyname Kind Ty Ty Step
 | Step_ifixL Ty Ty Ty Step
 | Step_ifixR Ty Ty Ty Step
 | Step_SOP (([]) (([]) Ty)) (([]) Ty) Ty Ty (([]) Ty) (([]) (([]) Ty)) 
 (ForallSet2 Ty ()) (ForallSet Ty ()) Step

step_rect :: (Prelude.String -> Kind -> Ty -> Ty -> () -> () -> a1) -> (Ty ->
             Ty -> Ty -> Step -> a1 -> a1) -> (Ty -> Ty -> Ty -> () -> Step
             -> a1 -> a1) -> (Ty -> Ty -> Ty -> Step -> a1 -> a1) -> (Ty ->
             Ty -> Ty -> () -> Step -> a1 -> a1) -> (BinderTyname -> Kind ->
             Ty -> Ty -> Step -> a1 -> a1) -> (BinderTyname -> Kind -> Ty ->
             Ty -> Step -> a1 -> a1) -> (Ty -> Ty -> Ty -> Step -> a1 -> a1)
             -> (Ty -> Ty -> Ty -> () -> Step -> a1 -> a1) -> ((([])
             (([]) Ty)) -> (([]) Ty) -> Ty -> Ty -> (([]) Ty) -> (([])
             (([]) Ty)) -> (ForallSet2 Ty ()) -> (ForallSet Ty ()) -> Step ->
             a1 -> a1) -> Ty -> Ty -> Step -> a1
step_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 _ _ s =
  case s of {
   Step_beta x k s0 t -> f0 x k s0 t __ __;
   Step_appL s1 s2 t s0 ->
    f1 s1 s2 t s0 (step_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s1 s2 s0);
   Step_appR s0 t1 t2 s1 ->
    f2 s0 t1 t2 __ s1 (step_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1 t2 s1);
   Step_funL s1 s2 t s0 ->
    f3 s1 s2 t s0 (step_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s1 s2 s0);
   Step_funR s0 t1 t2 s1 ->
    f4 s0 t1 t2 __ s1 (step_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1 t2 s1);
   Step_forall bX k s1 s2 s0 ->
    f5 bX k s1 s2 s0 (step_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s1 s2 s0);
   Step_abs bX k t1 t2 s0 ->
    f6 bX k t1 t2 s0 (step_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1 t2 s0);
   Step_ifixL f10 f11 t s0 ->
    f7 f10 f11 t s0 (step_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0);
   Step_ifixR f10 t1 t2 s0 ->
    f8 f10 t1 t2 __ s0 (step_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1 t2 s0);
   Step_SOP tss_normal tss_sub_normal tss_sub1 tss_sub2 tss_sub_remainder
    tss_remainder f10 f11 s0 ->
    f9 tss_normal tss_sub_normal tss_sub1 tss_sub2 tss_sub_remainder
      tss_remainder f10 f11 s0
      (step_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 tss_sub1 tss_sub2 s0)}

step_rec :: (Prelude.String -> Kind -> Ty -> Ty -> () -> () -> a1) -> (Ty ->
            Ty -> Ty -> Step -> a1 -> a1) -> (Ty -> Ty -> Ty -> () -> Step ->
            a1 -> a1) -> (Ty -> Ty -> Ty -> Step -> a1 -> a1) -> (Ty -> Ty ->
            Ty -> () -> Step -> a1 -> a1) -> (BinderTyname -> Kind -> Ty ->
            Ty -> Step -> a1 -> a1) -> (BinderTyname -> Kind -> Ty -> Ty ->
            Step -> a1 -> a1) -> (Ty -> Ty -> Ty -> Step -> a1 -> a1) -> (Ty
            -> Ty -> Ty -> () -> Step -> a1 -> a1) -> ((([]) (([]) Ty)) ->
            (([]) Ty) -> Ty -> Ty -> (([]) Ty) -> (([]) (([]) Ty)) ->
            (ForallSet2 Ty ()) -> (ForallSet Ty ()) -> Step -> a1 -> a1) ->
            Ty -> Ty -> Step -> a1
step_rec =
  step_rect

bind0 :: (Prelude.Maybe a1) -> (a1 -> Prelude.Maybe a2) -> Prelude.Maybe a2
bind0 xx f0 =
  case xx of {
   Prelude.Just a -> f0 a;
   Prelude.Nothing -> Prelude.Nothing}

solution_left :: a1 -> a2 -> a1 -> a2
solution_left _ x _ =
  x

solution_right :: a1 -> a2 -> a1 -> a2
solution_right _ x _ =
  x

data USort =
   Lam
 | ForAll

data BSort =
   App
 | IFix
 | Fun

data Term0 =
   Tmvar Prelude.String
 | Tmabs USort Prelude.String Kind Term0
 | Tmbin BSort Term0 Term0
 | Tmbuiltin DefaultUni

term_rect :: (Prelude.String -> a1) -> (USort -> Prelude.String -> Kind ->
             Term0 -> a1 -> a1) -> (BSort -> Term0 -> a1 -> Term0 -> a1 ->
             a1) -> (DefaultUni -> a1) -> Term0 -> a1
term_rect f0 f1 f2 f3 t =
  case t of {
   Tmvar s -> f0 s;
   Tmabs uSort s k t0 -> f1 uSort s k t0 (term_rect f0 f1 f2 f3 t0);
   Tmbin bSort t0 t1 ->
    f2 bSort t0 (term_rect f0 f1 f2 f3 t0) t1 (term_rect f0 f1 f2 f3 t1);
   Tmbuiltin d -> f3 d}

term_rec :: (Prelude.String -> a1) -> (USort -> Prelude.String -> Kind ->
            Term0 -> a1 -> a1) -> (BSort -> Term0 -> a1 -> Term0 -> a1 -> a1)
            -> (DefaultUni -> a1) -> Term0 -> a1
term_rec =
  term_rect

ftv0 :: Term0 -> ([]) Prelude.String
ftv0 t =
  case t of {
   Tmvar x -> (:) x ([]);
   Tmabs _ x _ t' ->
    remove ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
      x (ftv0 t');
   Tmbin _ t1 t2 -> app (ftv0 t1) (ftv0 t2);
   Tmbuiltin _ -> ([])}

btv :: Term0 -> ([]) Prelude.String
btv t =
  case t of {
   Tmabs _ x _ t' -> (:) x (btv t');
   Tmbin _ t1 t2 -> app (btv t1) (btv t2);
   _ -> ([])}

tv :: Term0 -> ([]) Prelude.String
tv s =
  case s of {
   Tmvar x -> (:) x ([]);
   Tmabs _ x _ s0 -> (:) x (tv s0);
   Tmbin _ s0 t -> app (tv s0) (tv t);
   Tmbuiltin _ -> ([])}

tv_keys_env :: (([]) ((,) Prelude.String Term0)) -> ([]) Prelude.String
tv_keys_env sigma =
  case sigma of {
   ([]) -> ([]);
   (:) p sigma' ->
    case p of {
     (,) x t -> (:) x (app (tv t) (tv_keys_env sigma'))}}

fresh2 :: (([]) ((,) Prelude.String Term0)) -> Term0 -> Prelude.String
fresh2 sigma t =
  append "a" (concat0 "" (app (tv_keys_env sigma) (tv t)))

rename0 :: Prelude.String -> Prelude.String -> Term0 -> Term0
rename0 x x' t =
  case t of {
   Tmvar y ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
           y of {
     Prelude.True -> Tmvar x';
     Prelude.False -> Tmvar y};
   Tmabs b y k1 t_body ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
           y of {
     Prelude.True -> Tmabs b y k1 t_body;
     Prelude.False -> Tmabs b y k1 (rename0 x x' t_body)};
   Tmbin b t1 t2 -> Tmbin b (rename0 x x' t1) (rename0 x x' t2);
   Tmbuiltin d -> Tmbuiltin d}

substituteTCA0 :: Prelude.String -> Term0 -> Term0 -> Term0
substituteTCA0 a a0 b =
  let {
   fix_F x =
     let {x0 = case x of {
                (,) pr1 _ -> pr1}} in
     let {u = case case x of {
                    (,) _ pr2 -> pr2} of {
               (,) pr1 _ -> pr1}} in
     let {
      substituteTCA1 = \a1 a2 b0 ->
       let {y = (,) a1 ((,) a2 b0)} in (\_ -> fix_F y)}
     in
     case case case x of {
                (,) _ pr2 -> pr2} of {
           (,) _ pr2 -> pr2} of {
      Tmvar s ->
       case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
              x0 s of {
        Prelude.True -> u;
        Prelude.False -> Tmvar s};
      Tmabs uSort s k t ->
       case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
              x0 s of {
        Prelude.True -> Tmabs uSort s k t;
        Prelude.False ->
         case existsb
                (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                  s) (ftv0 u) of {
          Prelude.True ->
           let {y' = fresh2 ((:) ((,) x0 u) ([])) t} in
           let {t' = rename0 s y' t} in
           Tmabs uSort y' k (substituteTCA1 x0 u t' __);
          Prelude.False -> Tmabs uSort s k (substituteTCA1 x0 u t __)}};
      Tmbin bSort t t0 -> Tmbin bSort (substituteTCA1 x0 u t __)
       (substituteTCA1 x0 u t0 __);
      Tmbuiltin d -> Tmbuiltin d}}
  in fix_F ((,) a ((,) a0 b))

lookup_app_or_extended :: Prelude.String -> a1 -> (([])
                          ((,) Prelude.String a1)) -> (([])
                          ((,) Prelude.String a1)) -> Prelude.Either 
                          () ()
lookup_app_or_extended y _ r1 _ =
  list_rec (\_ -> Prelude.Right __) (\a _ iHR1 _ ->
    case a of {
     (,) s _ ->
      let {
       b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             y s}
      in
      case b of {
       Prelude.True -> eq_rec_r s (\_ _ -> Prelude.Left __) y __ iHR1;
       Prelude.False ->
        eq_rec_r Prelude.False (iHR1 __)
          (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
            s y)}}) r1 __

lookup_split_app_helper :: (([]) ((,) Prelude.String Prelude.String)) ->
                           (([]) ((,) Prelude.String Prelude.String)) ->
                           Prelude.String -> Prelude.String -> Prelude.Either
                           () ()
lookup_split_app_helper r1 _ s s' =
  list_rec (\_ _ -> Prelude.Right __) (\a _ iHR1 _ _ ->
    case a of {
     (,) s0 s1 ->
      let {
       b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             s0 s}
      in
      case b of {
       Prelude.True ->
        eq_rec_r s (\_ ->
          eq_rec_r s' (eq_rec_r s' (\_ _ -> Prelude.Left __) s1 __ __) s1) s0
          __;
       Prelude.False ->
        let {s2 = iHR1 __ __} in
        case s2 of {
         Prelude.Left _ -> Prelude.Left __;
         Prelude.Right _ -> Prelude.Right __}}}) r1 __ __

data Star a e =
   StarR
 | StarSE a a (Star a e) e

star_rect :: a1 -> a3 -> (a1 -> a1 -> (Star a1 a2) -> a3 -> a2 -> a3) -> a1
             -> (Star a1 a2) -> a3
star_rect x f0 f1 _ s =
  case s of {
   StarR -> f0;
   StarSE y z s0 y0 -> f1 y z s0 (star_rect x f0 f1 y s0) y0}

star_rec :: a1 -> a3 -> (a1 -> a1 -> (Star a1 a2) -> a3 -> a2 -> a3) -> a1 ->
            (Star a1 a2) -> a3
star_rec =
  star_rect

list_diff :: (a1 -> a1 -> Prelude.Bool) -> (([]) a1) -> (([]) a1) -> ([]) a1
list_diff eq_dec l1 l2 =
  filter (\x ->
    case in_dec eq_dec x l2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}) l1

btv_env :: (([]) ((,) Prelude.String Term0)) -> ([]) Prelude.String
btv_env sigma =
  case sigma of {
   ([]) -> ([]);
   (:) p sigma' -> case p of {
                    (,) _ t -> app (btv t) (btv_env sigma')}}

psubs :: (([]) ((,) Prelude.String Term0)) -> Term0 -> Term0
psubs sigma t =
  case t of {
   Tmvar x ->
    case lookup x sigma of {
     Prelude.Just t0 -> t0;
     Prelude.Nothing -> Tmvar x};
   Tmabs b x a s -> Tmabs b x a (psubs sigma s);
   Tmbin b s t0 -> Tmbin b (psubs sigma s) (psubs sigma t0);
   Tmbuiltin d -> Tmbuiltin d}

data ParSeq =
   ParSeq_nil
 | ParSeq_cons Prelude.String Term0 (([]) ((,) Prelude.String Term0)) 
 ParSeq

sub :: Prelude.String -> Term0 -> Term0 -> Term0
sub x u t =
  case t of {
   Tmvar y ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
           y of {
     Prelude.True -> u;
     Prelude.False -> Tmvar y};
   Tmabs b y k1 t' -> Tmabs b y k1 (sub x u t');
   Tmbin b t1 t2 -> Tmbin b (sub x u t1) (sub x u t2);
   Tmbuiltin d -> Tmbuiltin d}

data Step_naive =
   Step_beta0 Prelude.String Kind Term0 Term0
 | Step_appL0 BSort Term0 Term0 Term0 Step_naive
 | Step_appR0 BSort Term0 Term0 Term0 Step_naive
 | Step_abs0 USort Prelude.String Kind Term0 Term0 Step_naive

step_naive_rect :: (Prelude.String -> Kind -> Term0 -> Term0 -> a1) -> (BSort
                   -> Term0 -> Term0 -> Term0 -> Step_naive -> a1 -> a1) ->
                   (BSort -> Term0 -> Term0 -> Term0 -> Step_naive -> a1 ->
                   a1) -> (USort -> Prelude.String -> Kind -> Term0 -> Term0
                   -> Step_naive -> a1 -> a1) -> Term0 -> Term0 -> Step_naive
                   -> a1
step_naive_rect f0 f1 f2 f3 _ _ s =
  case s of {
   Step_beta0 x a s0 t -> f0 x a s0 t;
   Step_appL0 b s1 s2 t s0 ->
    f1 b s1 s2 t s0 (step_naive_rect f0 f1 f2 f3 s1 s2 s0);
   Step_appR0 b s0 t1 t2 s1 ->
    f2 b s0 t1 t2 s1 (step_naive_rect f0 f1 f2 f3 t1 t2 s1);
   Step_abs0 b x a s1 s2 s0 ->
    f3 b x a s1 s2 s0 (step_naive_rect f0 f1 f2 f3 s1 s2 s0)}

step_naive_rec :: (Prelude.String -> Kind -> Term0 -> Term0 -> a1) -> (BSort
                  -> Term0 -> Term0 -> Term0 -> Step_naive -> a1 -> a1) ->
                  (BSort -> Term0 -> Term0 -> Term0 -> Step_naive -> a1 ->
                  a1) -> (USort -> Prelude.String -> Kind -> Term0 -> Term0
                  -> Step_naive -> a1 -> a1) -> Term0 -> Term0 -> Step_naive
                  -> a1
step_naive_rec =
  step_naive_rect

data AlphaVar =
   Alpha_var_refl Prelude.String
 | Alpha_var_cons Prelude.String Prelude.String (([])
                                                ((,) Prelude.String
                                                Prelude.String))
 | Alpha_var_diff Prelude.String Prelude.String Prelude.String Prelude.String 
 (([]) ((,) Prelude.String Prelude.String)) AlphaVar

alphaVar_rect :: (Prelude.String -> a1) -> (Prelude.String -> Prelude.String
                 -> (([]) ((,) Prelude.String Prelude.String)) -> a1) ->
                 (Prelude.String -> Prelude.String -> Prelude.String ->
                 Prelude.String -> (([]) ((,) Prelude.String Prelude.String))
                 -> () -> () -> AlphaVar -> a1 -> a1) -> (([])
                 ((,) Prelude.String Prelude.String)) -> Prelude.String ->
                 Prelude.String -> AlphaVar -> a1
alphaVar_rect f0 f1 f2 _ _ _ a =
  case a of {
   Alpha_var_refl x -> f0 x;
   Alpha_var_cons z w sigma -> f1 z w sigma;
   Alpha_var_diff x y z w sigma a0 ->
    f2 x y z w sigma __ __ a0 (alphaVar_rect f0 f1 f2 sigma z w a0)}

alphaVar_rec :: (Prelude.String -> a1) -> (Prelude.String -> Prelude.String
                -> (([]) ((,) Prelude.String Prelude.String)) -> a1) ->
                (Prelude.String -> Prelude.String -> Prelude.String ->
                Prelude.String -> (([]) ((,) Prelude.String Prelude.String))
                -> () -> () -> AlphaVar -> a1 -> a1) -> (([])
                ((,) Prelude.String Prelude.String)) -> Prelude.String ->
                Prelude.String -> AlphaVar -> a1
alphaVar_rec =
  alphaVar_rect

data Alpha =
   Alpha_var Prelude.String Prelude.String (([])
                                           ((,) Prelude.String
                                           Prelude.String)) AlphaVar
 | Alpha_lam USort Prelude.String Prelude.String Kind Term0 Term0 (([])
                                                                  ((,)
                                                                  Prelude.String
                                                                  Prelude.String)) 
 Alpha
 | Alpha_app BSort Term0 Term0 Term0 Term0 (([])
                                           ((,) Prelude.String
                                           Prelude.String)) Alpha Alpha
 | Alpha_builtin (([]) ((,) Prelude.String Prelude.String)) DefaultUni

alpha_rect :: (Prelude.String -> Prelude.String -> (([])
              ((,) Prelude.String Prelude.String)) -> AlphaVar -> a1) ->
              (USort -> Prelude.String -> Prelude.String -> Kind -> Term0 ->
              Term0 -> (([]) ((,) Prelude.String Prelude.String)) -> Alpha ->
              a1 -> a1) -> (BSort -> Term0 -> Term0 -> Term0 -> Term0 ->
              (([]) ((,) Prelude.String Prelude.String)) -> Alpha -> a1 ->
              Alpha -> a1 -> a1) -> ((([])
              ((,) Prelude.String Prelude.String)) -> DefaultUni -> a1) ->
              (([]) ((,) Prelude.String Prelude.String)) -> Term0 -> Term0 ->
              Alpha -> a1
alpha_rect f0 f1 f2 f3 _ _ _ a =
  case a of {
   Alpha_var x y sigma a0 -> f0 x y sigma a0;
   Alpha_lam b x y a0 s1 s2 sigma a1 ->
    f1 b x y a0 s1 s2 sigma a1
      (alpha_rect f0 f1 f2 f3 ((:) ((,) x y) sigma) s1 s2 a1);
   Alpha_app b s1 s2 t1 t2 sigma a0 a1 ->
    f2 b s1 s2 t1 t2 sigma a0 (alpha_rect f0 f1 f2 f3 sigma s1 s2 a0) a1
      (alpha_rect f0 f1 f2 f3 sigma t1 t2 a1);
   Alpha_builtin r d -> f3 r d}

alpha_rec :: (Prelude.String -> Prelude.String -> (([])
             ((,) Prelude.String Prelude.String)) -> AlphaVar -> a1) ->
             (USort -> Prelude.String -> Prelude.String -> Kind -> Term0 ->
             Term0 -> (([]) ((,) Prelude.String Prelude.String)) -> Alpha ->
             a1 -> a1) -> (BSort -> Term0 -> Term0 -> Term0 -> Term0 -> (([])
             ((,) Prelude.String Prelude.String)) -> Alpha -> a1 -> Alpha ->
             a1 -> a1) -> ((([]) ((,) Prelude.String Prelude.String)) ->
             DefaultUni -> a1) -> (([]) ((,) Prelude.String Prelude.String))
             -> Term0 -> Term0 -> Alpha -> a1
alpha_rec =
  alpha_rect

data AlphaCtxRefl =
   Alpha_refl_nil
 | Alpha_refl_cons Prelude.String (([]) ((,) Prelude.String Prelude.String)) 
 AlphaCtxRefl

alphaCtxRefl_rect :: a1 -> (Prelude.String -> (([])
                     ((,) Prelude.String Prelude.String)) -> AlphaCtxRefl ->
                     a1 -> a1) -> (([]) ((,) Prelude.String Prelude.String))
                     -> AlphaCtxRefl -> a1
alphaCtxRefl_rect f0 f1 _ a =
  case a of {
   Alpha_refl_nil -> f0;
   Alpha_refl_cons x ren a0 -> f1 x ren a0 (alphaCtxRefl_rect f0 f1 ren a0)}

alphaCtxRefl_rec :: a1 -> (Prelude.String -> (([])
                    ((,) Prelude.String Prelude.String)) -> AlphaCtxRefl ->
                    a1 -> a1) -> (([]) ((,) Prelude.String Prelude.String))
                    -> AlphaCtxRefl -> a1
alphaCtxRefl_rec =
  alphaCtxRefl_rect

alphavar_refl :: Prelude.String -> (([]) ((,) Prelude.String Prelude.String))
                 -> AlphaCtxRefl -> AlphaVar
alphavar_refl s ren halphactx =
  alphaCtxRefl_rec (Alpha_var_refl s) (\x ren0 _ iHHalphactx ->
    let {
     b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
           s}
    in
    case b of {
     Prelude.True -> eq_rec_r s (Alpha_var_cons s s ren0) x;
     Prelude.False -> Alpha_var_diff x x s s ren0 iHHalphactx}) ren halphactx

alpha_refl :: Term0 -> (([]) ((,) Prelude.String Prelude.String)) ->
              AlphaCtxRefl -> Alpha
alpha_refl s ren =
  term_rec (\s0 ren0 hid -> Alpha_var s0 s0 ren0 (alphavar_refl s0 ren0 hid))
    (\uSort s0 k s1 iHs ren0 hid -> Alpha_lam uSort s0 s0 k s1 s1 ren0
    (iHs ((:) ((,) s0 s0) ren0) (Alpha_refl_cons s0 ren0 hid)))
    (\bSort s1 iHs1 s2 iHs2 ren0 hid -> Alpha_app bSort s1 s1 s2 s2 ren0
    (iHs1 ren0 hid) (iHs2 ren0 hid)) (\d ren0 _ -> Alpha_builtin ren0 d) s
    ren

data AlphaCtxSym =
   Alpha_sym_nil
 | Alpha_sym_cons Prelude.String Prelude.String (([])
                                                ((,) Prelude.String
                                                Prelude.String)) (([])
                                                                 ((,)
                                                                 Prelude.String
                                                                 Prelude.String)) 
 AlphaCtxSym

alphaCtxSym_rect :: a1 -> (Prelude.String -> Prelude.String -> (([])
                    ((,) Prelude.String Prelude.String)) -> (([])
                    ((,) Prelude.String Prelude.String)) -> AlphaCtxSym -> a1
                    -> a1) -> (([]) ((,) Prelude.String Prelude.String)) ->
                    (([]) ((,) Prelude.String Prelude.String)) -> AlphaCtxSym
                    -> a1
alphaCtxSym_rect f0 f1 _ _ a =
  case a of {
   Alpha_sym_nil -> f0;
   Alpha_sym_cons x y ren ren' a0 ->
    f1 x y ren ren' a0 (alphaCtxSym_rect f0 f1 ren ren' a0)}

alphaCtxSym_rec :: a1 -> (Prelude.String -> Prelude.String -> (([])
                   ((,) Prelude.String Prelude.String)) -> (([])
                   ((,) Prelude.String Prelude.String)) -> AlphaCtxSym -> a1
                   -> a1) -> (([]) ((,) Prelude.String Prelude.String)) ->
                   (([]) ((,) Prelude.String Prelude.String)) -> AlphaCtxSym
                   -> a1
alphaCtxSym_rec =
  alphaCtxSym_rect

alpha_sym :: Term0 -> Term0 -> (([]) ((,) Prelude.String Prelude.String)) ->
             (([]) ((,) Prelude.String Prelude.String)) -> AlphaCtxSym ->
             Alpha -> Alpha
alpha_sym s t ren ren' hsym halpha =
  alpha_rec (\x y sigma a ren'0 hsym0 -> Alpha_var y x ren'0
    (alphaCtxSym_rec (\y0 x0 a0 ->
      case a0 of {
       Alpha_var_refl x1 ->
        eq_rec_r x0 (\_ -> eq_rec_r y0 (Alpha_var_refl y0) x0) x1 __;
       Alpha_var_cons _ _ _ -> false_rec __ __;
       Alpha_var_diff _ _ _ _ _ x1 -> false_rec __ __ __ __ x1})
      (\x0 y0 ren0 ren'1 _ iHHsym y1 x1 a0 ->
      case a0 of {
       Alpha_var_refl _ -> false_rec __ __;
       Alpha_var_cons z w sigma0 ->
        eq_rec_r x0 (\_ ->
          eq_rec_r y0 (\_ ->
            eq_rec_r ren0 (\_ ->
              eq_rec_r x1 (\_ ->
                eq_rec_r y1
                  (eq_rec_r x1 (\a1 ->
                    eq_rec_r y1 (\_ -> Alpha_var_cons y1 x1 ren'1) y0 a1) x0
                    a0) y0) x0) sigma0) w) z __ __ __ __;
       Alpha_var_diff x2 y2 z w sigma0 x3 ->
        eq_rec_r x0 (\_ ->
          eq_rec_r y0 (\_ ->
            eq_rec_r ren0 (\_ ->
              eq_rec_r x1 (\_ ->
                eq_rec_r y1 (\_ _ h6 -> Alpha_var_diff y0 x0 y1 x1 ren'1
                  (iHHsym y1 x1 h6)) w) z) sigma0) y2) x2 __ __ __ __ __ __
          x3}) sigma ren'0 hsym0 y x a))
    (\b x y a s1 s2 sigma _ iHHalpha ren'0 hsym0 -> Alpha_lam b y x a s2 s1
    ren'0
    (iHHalpha ((:) ((,) y x) ren'0) (Alpha_sym_cons x y sigma ren'0 hsym0)))
    (\b s1 s2 t1 t2 _ _ iHHalpha1 _ iHHalpha2 ren'0 hsym0 -> Alpha_app b s2
    s1 t2 t1 ren'0 (iHHalpha1 ren'0 hsym0) (iHHalpha2 ren'0 hsym0))
    (\_ d ren'0 _ -> Alpha_builtin ren'0 d) ren s t halpha ren' hsym

data Coq__UU03b1_CtxTrans =
   Alpha_trans_nil
 | Alpha_trans_cons Prelude.String Prelude.String Prelude.String (([])
                                                                 ((,)
                                                                 Prelude.String
                                                                 Prelude.String)) 
 (([]) ((,) Prelude.String Prelude.String)) (([])
                                            ((,) Prelude.String
                                            Prelude.String)) Coq__UU03b1_CtxTrans

alpha_var_trans :: Prelude.String -> Prelude.String -> Prelude.String ->
                   (([]) ((,) Prelude.String Prelude.String)) -> (([])
                   ((,) Prelude.String Prelude.String)) -> (([])
                   ((,) Prelude.String Prelude.String)) ->
                   Coq__UU03b1_CtxTrans -> AlphaVar -> AlphaVar -> AlphaVar
alpha_var_trans s t u ren ren' ren'' htrans halpha1 halpha2 =
  alphaVar_rec (\_ _ _ _ htrans0 halpha3 ->
    case htrans0 of {
     Alpha_trans_nil -> halpha3;
     Alpha_trans_cons _ _ _ _ _ _ x -> false_rec __ __ x})
    (\z w sigma u0 _ _ htrans0 halpha3 ->
    case htrans0 of {
     Alpha_trans_nil -> false_rec __ __;
     Alpha_trans_cons x y z0 ren0 ren'0 ren''0 x0 ->
      eq_rec_r z (\_ ->
        eq_rec_r w (\_ ->
          eq_rec_r sigma (\_ _ _ ->
            case halpha3 of {
             Alpha_var_refl _ -> false_rec __ __;
             Alpha_var_cons z1 w0 sigma0 ->
              eq_rec_r w (\_ ->
                eq_rec_r z0 (\_ ->
                  eq_rec_r ren'0 (\_ ->
                    eq_rec_r w (\_ ->
                      eq_rec_r u0
                        (eq_rec_r u0 (\_ _ -> Alpha_var_cons z u0 ren''0) z0
                          halpha3 htrans0) z0) w) sigma0) w0) z1 __ __ __ __;
             Alpha_var_diff x1 y0 z1 w0 sigma0 x2 ->
              eq_rec_r w (\_ ->
                eq_rec_r z0 (\_ ->
                  eq_rec_r ren'0 (\_ ->
                    eq_rec_r w (\_ -> eq_rec_r u0 (\_ _ _ -> false_rec) w0)
                      z1) sigma0) y0) x1 __ __ __ __ __ __ x2}) ren0) y) x __
        __ __ __ x0})
    (\x y z w sigma _ _ _ iHHalpha1 u0 _ _ htrans0 halpha3 ->
    case htrans0 of {
     Alpha_trans_nil -> false_rec __ __;
     Alpha_trans_cons x0 y0 z0 ren0 ren'0 ren''0 x1 ->
      eq_rec_r x (\_ ->
        eq_rec_r y (\_ ->
          eq_rec_r sigma (\_ _ h4 ->
            case halpha3 of {
             Alpha_var_refl _ -> false_rec __ __;
             Alpha_var_cons z1 w0 sigma0 ->
              eq_rec_r y (\_ ->
                eq_rec_r z0 (\_ ->
                  eq_rec_r ren'0 (\_ ->
                    eq_rec_r w (\_ ->
                      eq_rec_r u0
                        (eq_rec_r w (\_ halpha4 htrans1 ->
                          eq_rec_r u0 (\_ _ -> false_rec) z0 halpha4 htrans1)
                          y __ halpha3 htrans0) z0) y) sigma0) w0) z1 __ __
                __ __;
             Alpha_var_diff x2 y1 z1 w0 sigma0 x3 ->
              eq_rec_r y (\_ ->
                eq_rec_r z0 (\_ ->
                  eq_rec_r ren'0 (\_ ->
                    eq_rec_r w (\_ ->
                      eq_rec_r u0 (\_ _ h7 -> Alpha_var_diff x z0 z u0 ren''0
                        (iHHalpha1 u0 ren''0 ren'0 h4 h7)) w0) z1) sigma0) y1)
                x2 __ __ __ __ __ __ x3}) ren0) y0) x0 __ __ __ __ x1}) ren s
    t halpha1 u ren'' ren' htrans halpha2

alpha_trans :: Term0 -> Term0 -> Term0 -> (([])
               ((,) Prelude.String Prelude.String)) -> (([])
               ((,) Prelude.String Prelude.String)) -> (([])
               ((,) Prelude.String Prelude.String)) -> Coq__UU03b1_CtxTrans
               -> Alpha -> Alpha -> Alpha
alpha_trans s t u ren ren' ren'' htrans halpha1 halpha2 =
  alpha_rec (\x y sigma a _ ren''0 ren'0 htrans0 halpha3 ->
    case halpha3 of {
     Alpha_var x0 y0 sigma0 x1 ->
      eq_rec_r ren'0 (\_ ->
        eq_rec_r y (\_ h1 -> Alpha_var x y0 ren''0
          (alpha_var_trans x y y0 sigma ren'0 ren''0 htrans0 a h1)) x0)
        sigma0 __ __ x1;
     Alpha_lam _ _ _ _ _ _ sigma0 x0 ->
      eq_rec_r ren'0 (\_ -> false_rec) sigma0 __ __ x0;
     Alpha_app _ _ _ _ _ sigma0 x0 x1 ->
      eq_rec_r ren'0 (\_ -> false_rec) sigma0 __ __ x0 x1;
     Alpha_builtin r _ -> eq_rec_r ren'0 (\_ -> false_rec) r __ __})
    (\b x y a s1 s2 sigma _ iHHalpha1 _ ren''0 ren'0 htrans0 halpha3 ->
    case halpha3 of {
     Alpha_var _ _ sigma0 x0 ->
      eq_rec_r ren'0 (\_ -> false_rec) sigma0 __ __ x0;
     Alpha_lam b0 x0 y0 a0 s3 s4 sigma0 x1 ->
      eq_rec_r ren'0 (\_ ->
        eq_rec_r b (\_ ->
          eq_rec_r y (\_ ->
            eq_rec_r a (\_ ->
              eq_rec_r s2 (\_ _ -> Alpha_lam b x y0 a s1 s4 ren''0
                (iHHalpha1 s4 ((:) ((,) x y0) ren''0) ((:) ((,) y y0) ren'0)
                  (Alpha_trans_cons x y y0 sigma ren'0 ren''0 htrans0)
                  (case halpha3 of {
                    Alpha_var _ _ sigma1 x2 ->
                     eq_rec_r ren'0 (\_ -> false_rec) sigma1 __ __ x2;
                    Alpha_lam b1 x2 y1 a1 s5 s6 sigma1 x3 ->
                     eq_rec_r ren'0 (\_ ->
                       eq_rec_r b (\_ ->
                         eq_rec_r y (\_ ->
                           eq_rec_r a (\_ ->
                             eq_rec_r s2 (\_ ->
                               eq_rec_r y0 (\_ -> eq_rec_r s4 (\h1 -> h1) s6)
                                 y1 __) s5) a1) x2) b1 __ __ __) sigma1 __ __
                       x3;
                    Alpha_app _ _ _ _ _ sigma1 x2 x3 ->
                     eq_rec_r ren'0 (\_ -> false_rec) sigma1 __ __ x2 x3;
                    Alpha_builtin r _ ->
                     eq_rec_r ren'0 (\_ -> false_rec) r __ __}))) s3) a0) x0)
          b0 __ __ __) sigma0 __ __ x1;
     Alpha_app _ _ _ _ _ sigma0 x0 x1 ->
      eq_rec_r ren'0 (\_ -> false_rec) sigma0 __ __ x0 x1;
     Alpha_builtin r _ -> eq_rec_r ren'0 (\_ -> false_rec) r __ __})
    (\b s1 s2 t1 t2 _ _ iHHalpha1_1 _ iHHalpha1_2 _ ren''0 ren'0 htrans0 halpha3 ->
    case halpha3 of {
     Alpha_var _ _ sigma x -> eq_rec_r ren'0 (\_ -> false_rec) sigma __ __ x;
     Alpha_lam _ _ _ _ _ _ sigma x ->
      eq_rec_r ren'0 (\_ -> false_rec) sigma __ __ x;
     Alpha_app b0 s3 s4 t3 t4 sigma x x0 ->
      eq_rec_r ren'0 (\_ ->
        eq_rec_r b (\_ ->
          eq_rec_r s2 (\_ ->
            eq_rec_r t2 (\_ h4 h5 -> Alpha_app b s1 s4 t1 t4 ren''0
              (iHHalpha1_1 s4 ren''0 ren'0 htrans0 h4)
              (iHHalpha1_2 t4 ren''0 ren'0 htrans0 h5)) t3) s3) b0 __ __)
        sigma __ __ x x0;
     Alpha_builtin r _ -> eq_rec_r ren'0 (\_ -> false_rec) r __ __})
    (\_ d _ ren''0 ren'0 _ halpha3 ->
    case halpha3 of {
     Alpha_var _ _ sigma x -> eq_rec_r ren'0 (\_ -> false_rec) sigma __ __ x;
     Alpha_lam _ _ _ _ _ _ sigma x ->
      eq_rec_r ren'0 (\_ -> false_rec) sigma __ __ x;
     Alpha_app _ _ _ _ _ sigma x x0 ->
      eq_rec_r ren'0 (\_ -> false_rec) sigma __ __ x x0;
     Alpha_builtin r d0 ->
      eq_rec_r ren'0 (\_ -> eq_rec_r d (\_ -> Alpha_builtin ren''0 d) d0) r
        __ __}) ren s t halpha1 u ren'' ren' htrans halpha2

sym_alpha_ctx :: (([]) ((,) Prelude.String Prelude.String)) -> ([])
                 ((,) Prelude.String Prelude.String)
sym_alpha_ctx ren =
  case ren of {
   ([]) -> ([]);
   (:) p ren' -> case p of {
                  (,) x y -> (:) ((,) y x) (sym_alpha_ctx ren')}}

sym_alpha_ctx_is_sym :: (([]) ((,) Prelude.String Prelude.String)) ->
                        AlphaCtxSym
sym_alpha_ctx_is_sym ren =
  list_rec Alpha_sym_nil (\a ren0 iHren ->
    case a of {
     (,) s s0 -> Alpha_sym_cons s s0 ren0 (sym_alpha_ctx ren0) iHren}) ren

sym_alpha_ctx_left_is_sym :: (([]) ((,) Prelude.String Prelude.String)) ->
                             AlphaCtxSym
sym_alpha_ctx_left_is_sym ren =
  list_rec Alpha_sym_nil (\a ren0 iHren ->
    case a of {
     (,) s s0 -> Alpha_sym_cons s0 s (sym_alpha_ctx ren0) ren0 iHren}) ren

data IdCtx =
   Id_ctx_nil
 | Id_ctx_cons Prelude.String (([]) ((,) Prelude.String Prelude.String)) 
 IdCtx

idCtx_rect :: a1 -> (Prelude.String -> (([])
              ((,) Prelude.String Prelude.String)) -> IdCtx -> a1 -> a1) ->
              (([]) ((,) Prelude.String Prelude.String)) -> IdCtx -> a1
idCtx_rect f0 f1 _ i =
  case i of {
   Id_ctx_nil -> f0;
   Id_ctx_cons x ren i0 -> f1 x ren i0 (idCtx_rect f0 f1 ren i0)}

idCtx_rec :: a1 -> (Prelude.String -> (([])
             ((,) Prelude.String Prelude.String)) -> IdCtx -> a1 -> a1) ->
             (([]) ((,) Prelude.String Prelude.String)) -> IdCtx -> a1
idCtx_rec =
  idCtx_rect

data NotBreakShadowing =
   Not_break_shadow_nil Prelude.String
 | Not_break_shadow_cons Prelude.String Prelude.String Prelude.String 
 (([]) ((,) Prelude.String Prelude.String)) NotBreakShadowing
 | Not_break_shadow_id Prelude.String (([])
                                      ((,) Prelude.String Prelude.String))

idCtxNotBreakShadowing :: Prelude.String -> (([])
                          ((,) Prelude.String Prelude.String)) -> IdCtx ->
                          NotBreakShadowing
idCtxNotBreakShadowing x ren hid =
  list_rec (\_ -> Not_break_shadow_nil x) (\a ren0 iHren hid0 ->
    case a of {
     (,) s s0 ->
      eq_rec_r s0 (\hid1 ->
        let {
         b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
               x s0}
        in
        case b of {
         Prelude.True ->
          eq_rec_r s0 (\_ -> Not_break_shadow_id s0 ren0) x iHren;
         Prelude.False -> Not_break_shadow_cons x s0 s0 ren0
          (case hid1 of {
            Id_ctx_nil -> false_rec;
            Id_ctx_cons x0 ren1 x1 ->
             eq_rec_r s0 (\_ ->
               eq_rec_r s0 (\_ -> eq_rec_r ren0 iHren ren1) s0) x0 __ __ x1})})
        s hid0}) ren hid

data LegalRenSwap =
   Lrs_nil
 | Lrs_cons Prelude.String Prelude.String (([])
                                          ((,) Prelude.String Prelude.String)) 
 (([]) ((,) Prelude.String Prelude.String)) LegalRenSwap
 | Lrs_start Prelude.String Prelude.String Prelude.String Prelude.String 
 (([]) ((,) Prelude.String Prelude.String)) (([])
                                            ((,) Prelude.String
                                            Prelude.String)) LegalRenSwap

legalRenSwap_rect :: a1 -> (Prelude.String -> Prelude.String -> (([])
                     ((,) Prelude.String Prelude.String)) -> (([])
                     ((,) Prelude.String Prelude.String)) -> LegalRenSwap ->
                     a1 -> a1) -> (Prelude.String -> Prelude.String ->
                     Prelude.String -> Prelude.String -> (([])
                     ((,) Prelude.String Prelude.String)) -> (([])
                     ((,) Prelude.String Prelude.String)) -> () -> () ->
                     LegalRenSwap -> a1 -> a1) -> (([])
                     ((,) Prelude.String Prelude.String)) -> (([])
                     ((,) Prelude.String Prelude.String)) -> LegalRenSwap ->
                     a1
legalRenSwap_rect f0 f1 f2 _ _ l1 =
  case l1 of {
   Lrs_nil -> f0;
   Lrs_cons x y ren1 ren1' l ->
    f1 x y ren1 ren1' l (legalRenSwap_rect f0 f1 f2 ren1 ren1' l);
   Lrs_start x y v w ren1 ren1' l ->
    f2 x y v w ren1 ren1' __ __ l (legalRenSwap_rect f0 f1 f2 ren1 ren1' l)}

legalRenSwap_rec :: a1 -> (Prelude.String -> Prelude.String -> (([])
                    ((,) Prelude.String Prelude.String)) -> (([])
                    ((,) Prelude.String Prelude.String)) -> LegalRenSwap ->
                    a1 -> a1) -> (Prelude.String -> Prelude.String ->
                    Prelude.String -> Prelude.String -> (([])
                    ((,) Prelude.String Prelude.String)) -> (([])
                    ((,) Prelude.String Prelude.String)) -> () -> () ->
                    LegalRenSwap -> a1 -> a1) -> (([])
                    ((,) Prelude.String Prelude.String)) -> (([])
                    ((,) Prelude.String Prelude.String)) -> LegalRenSwap ->
                    a1
legalRenSwap_rec =
  legalRenSwap_rect

type LegalRenSwaps =
  Star (([]) ((,) Prelude.String Prelude.String)) LegalRenSwap

legalRenSwap_id :: (([]) ((,) Prelude.String Prelude.String)) -> LegalRenSwap
legalRenSwap_id ren =
  list_rec Lrs_nil (\a ren0 iHren ->
    case a of {
     (,) s s0 -> Lrs_cons s s0 ren0 ren0 iHren}) ren

lrs_sym :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
           ((,) Prelude.String Prelude.String)) -> LegalRenSwap ->
           LegalRenSwap
lrs_sym ren1 ren2 hlrs =
  legalRenSwap_rec (legalRenSwap_id ([])) (\x y ren3 ren1' _ iHHlrs ->
    Lrs_cons x y ren1' ren3 iHHlrs) (\x y v w ren3 ren1' _ _ _ iHHlrs ->
    Lrs_start v w x y ren1' ren3 iHHlrs) ren1 ren2 hlrs

lrss_cons :: Prelude.String -> Prelude.String -> (([])
             ((,) Prelude.String Prelude.String)) -> (([])
             ((,) Prelude.String Prelude.String)) -> LegalRenSwaps ->
             LegalRenSwaps
lrss_cons x y ren1 ren2 h =
  star_rec ren1 StarR (\y0 z _ iHstar e -> StarSE ((:) ((,) x y) y0) ((:)
    ((,) x y) z) iHstar (Lrs_cons x y y0 z e)) ren2 h

lrss_intro :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
              ((,) Prelude.String Prelude.String)) -> LegalRenSwap ->
              LegalRenSwaps
lrss_intro ren1 ren2 x =
  StarSE ren1 ren2 StarR x

lrss_left :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
             ((,) Prelude.String Prelude.String)) -> (([])
             ((,) Prelude.String Prelude.String)) -> LegalRenSwap ->
             LegalRenSwaps -> LegalRenSwaps
lrss_left ren1 ren2 ren3 hlrs hlrss =
  star_rec ren2 (lrss_intro ren1 ren2 hlrs) (\y z _ iHHlrss e -> StarSE y z
    iHHlrss e) ren3 hlrss

lrss_sym :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
            ((,) Prelude.String Prelude.String)) -> LegalRenSwaps ->
            LegalRenSwaps
lrss_sym ren1 ren2 h =
  star_rec ren1 StarR (\y z _ iHstar e ->
    lrss_left z y ren1 (lrs_sym y z e) iHstar) ren2 h

lrss_trans :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
              ((,) Prelude.String Prelude.String)) -> (([])
              ((,) Prelude.String Prelude.String)) -> LegalRenSwaps ->
              LegalRenSwaps -> LegalRenSwaps
lrss_trans ren1 ren2 ren3 hlrs12 hlrs23 =
  star_rec ren1 (\_ hlrs24 -> hlrs24) (\y z _ iHHlrs12 e ren4 hlrs24 ->
    iHHlrs12 ren4
      (let {hlrs25 = lrss_sym z ren4 hlrs24} in
       lrss_sym ren4 y (let {e0 = lrs_sym y z e} in StarSE z y hlrs25 e0)))
    ren2 hlrs12 ren3 hlrs23

alphavar_weaken :: Prelude.String -> Prelude.String -> (([])
                   ((,) Prelude.String Prelude.String)) -> Prelude.String ->
                   Prelude.String -> AlphaVar -> AlphaVar
alphavar_weaken v w ren s t halpha =
  case halpha of {
   Alpha_var_refl _ -> false_rec __ __;
   Alpha_var_cons z w0 sigma ->
    eq_rec_r v (\_ ->
      eq_rec_r w (\_ ->
        eq_rec_r ren (\_ ->
          eq_rec_r s (\_ ->
            eq_rec_r t
              (eq_rec_r s (\_ halpha0 ->
                eq_rec_r t (\_ _ -> false_rec) w __ halpha0) v __ halpha) w)
            v) sigma) w0) z __ __ __ __;
   Alpha_var_diff x y z w0 sigma x0 ->
    eq_rec_r v (\_ ->
      eq_rec_r w (\_ ->
        eq_rec_r ren (\_ ->
          eq_rec_r s (\_ -> eq_rec_r t (\_ _ h6 -> h6) w0) z) sigma) y) x __
      __ __ __ __ __ x0}

alphavar_swap :: Prelude.String -> Prelude.String -> (([])
                 ((,) Prelude.String Prelude.String)) -> (([])
                 ((,) Prelude.String Prelude.String)) -> LegalRenSwap ->
                 AlphaVar -> AlphaVar
alphavar_swap s t ren ren' hswap halpha =
  alphaVar_rec (\x _ hswap0 ->
    case hswap0 of {
     Lrs_nil -> Alpha_var_refl x;
     Lrs_cons _ _ _ _ x0 -> false_rec __ x0;
     Lrs_start _ _ _ _ _ _ x0 -> false_rec __ __ __ x0})
    (\z w sigma _ hswap0 ->
    case hswap0 of {
     Lrs_nil -> false_rec __;
     Lrs_cons x y ren1 ren1' x0 ->
      eq_rec_r z (\_ ->
        eq_rec_r w (\_ ->
          eq_rec_r sigma (\_ _ -> Alpha_var_cons z w ren1') ren1) y) x __ __
        __ x0;
     Lrs_start x y v w0 _ ren1' x0 ->
      eq_rec_r z (\_ ->
        eq_rec_r w (\_ _ _ _ _ -> Alpha_var_diff v w0 z w ((:) ((,) z w)
          ren1') (Alpha_var_cons z w ren1')) y) x __ __ __ __ __ x0})
    (\x y z w sigma _ _ halpha0 iHHalpha ren'0 hswap0 ->
    let {gen_x = (:) ((,) x y) sigma} in
    legalRenSwap_rec (\_ _ _ _ _ _ _ _ -> false_rec)
      (\x0 y0 ren1 ren1' hswap1 iHHswap x1 y1 sigma0 _ _ halpha1 iHHalpha0 _ ->
      solution_left sigma0
        (\ren1'0 hswap2 iHHswap0 x2 y2 _ _ halpha2 iHHalpha1 _ ->
        solution_left y2
          (\sigma1 ren1'1 hswap3 iHHswap1 x3 _ _ halpha3 iHHalpha2 _ ->
          solution_left x3 (\y3 _ ren1'2 hswap4 _ _ _ _ iHHalpha3 ->
            Alpha_var_diff x3 y3 z w ren1'2 (iHHalpha3 ren1'2 hswap4)) x0 y2
            sigma1 ren1'1 hswap3 iHHswap1 __ __ halpha3 iHHalpha2) y0 sigma0
          ren1'0 hswap2 iHHswap0 x2 __ __ halpha2 iHHalpha1) ren1 ren1'
        hswap1 iHHswap x1 y1 __ __ halpha1 iHHalpha0 __ __)
      (\x0 y0 v w0 ren1 ren1' _ _ hswap1 iHHswap x1 y1 sigma0 _ _ halpha1 iHHalpha0 _ ->
      solution_right ((:) ((,) v w0) ren1) (\_ _ halpha2 iHHalpha1 _ ->
        solution_left y1
          (\v0 w1 ren2 ren1'0 _ _ hswap2 iHHswap0 x2 _ _ halpha3 iHHalpha2 _ ->
          solution_left x2
            (\y2 v1 w2 ren3 ren1'1 _ _ hswap3 _ _ _ halpha4 iHHalpha3 ->
            let {
             b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                   v1 z}
            in
            case b of {
             Prelude.True ->
              eq_rec_r z (\_ halpha5 iHHalpha4 _ ->
                eq_rec_r w (\_ _ _ -> Alpha_var_cons z w ((:) ((,) x2 y2)
                  ren1'1)) w2 __ iHHalpha4 halpha5) v1 __ halpha4 iHHalpha3
                __;
             Prelude.False -> Alpha_var_diff v1 w2 z w ((:) ((,) x2 y2)
              ren1'1) (Alpha_var_diff x2 y2 z w ren1'1
              (let {
                iHHalpha4 = iHHalpha3 ((:) ((,) v1 w2) ren1'1) (Lrs_cons v1
                              w2 ren3 ren1'1 hswap3)}
               in
               alphavar_weaken v1 w2 ren1'1 z w iHHalpha4))}) x0 y1 v0 w1
            ren2 ren1'0 __ __ hswap2 iHHswap0 __ __ halpha3 iHHalpha2) y0 v
          w0 ren1 ren1' __ __ hswap1 iHHswap x1 __ __ halpha2 iHHalpha1)
        sigma0 __ __ halpha1 iHHalpha0 __ __) gen_x ren'0 hswap0 x y sigma __
      __ halpha0 iHHalpha __) ren s t halpha ren' hswap

alpha_swap :: Term0 -> Term0 -> (([]) ((,) Prelude.String Prelude.String)) ->
              (([]) ((,) Prelude.String Prelude.String)) -> LegalRenSwap ->
              Alpha -> Alpha
alpha_swap s t ren' ren hswap halpha =
  alpha_rec (\x y sigma a ren'0 lrs -> Alpha_var x y ren'0
    (alphavar_swap x y sigma ren'0 lrs a))
    (\b x y a s1 s2 sigma _ iHHalpha ren'0 lrs -> Alpha_lam b x y a s1 s2
    ren'0
    (let {hlrs_xy = Lrs_cons x y sigma ren'0 lrs} in
     iHHalpha ((:) ((,) x y) ren'0) hlrs_xy))
    (\b s1 s2 t1 t2 _ _ iHHalpha1 _ iHHalpha2 ren'0 lrs -> Alpha_app b s1 s2
    t1 t2 ren'0 (iHHalpha1 ren'0 lrs) (iHHalpha2 ren'0 lrs)) (\_ d ren'0 _ ->
    Alpha_builtin ren'0 d) ren s t halpha ren' hswap

alpha_swaps :: Term0 -> Term0 -> (([]) ((,) Prelude.String Prelude.String))
               -> (([]) ((,) Prelude.String Prelude.String)) -> LegalRenSwaps
               -> Alpha -> Alpha
alpha_swaps s t ren' ren hlrss ha =
  star_rec ren ha (\y z _ iHHlrss e -> alpha_swap s t z y e iHHlrss) ren'
    hlrss

ctx_id_left :: (([]) ((,) Prelude.String Prelude.String)) -> ([])
               ((,) Prelude.String Prelude.String)
ctx_id_left ren =
  case ren of {
   ([]) -> ([]);
   (:) p ren' -> case p of {
                  (,) x _ -> (:) ((,) x x) (ctx_id_left ren')}}

ctx_id_right :: (([]) ((,) Prelude.String Prelude.String)) -> ([])
                ((,) Prelude.String Prelude.String)
ctx_id_right ren =
  case ren of {
   ([]) -> ([]);
   (:) p ren' -> case p of {
                  (,) _ y -> (:) ((,) y y) (ctx_id_right ren')}}

ctx_id_left_is_id :: (([]) ((,) Prelude.String Prelude.String)) -> IdCtx
ctx_id_left_is_id ren =
  list_rec Id_ctx_nil (\a ren0 iHren ->
    case a of {
     (,) s _ -> Id_ctx_cons s (ctx_id_left ren0) iHren}) ren

ctx_id_right_is_id :: (([]) ((,) Prelude.String Prelude.String)) -> IdCtx
ctx_id_right_is_id ren =
  list_rec Id_ctx_nil (\a ren0 iHren ->
    case a of {
     (,) _ s -> Id_ctx_cons s (ctx_id_right ren0) iHren}) ren

id_left_trans :: (([]) ((,) Prelude.String Prelude.String)) ->
                 Coq__UU03b1_CtxTrans
id_left_trans ren =
  list_rec Alpha_trans_nil (\a ren0 iHren ->
    case a of {
     (,) s s0 -> Alpha_trans_cons s s s0 (ctx_id_left ren0) ren0 ren0 iHren})
    ren

id_right_trans :: (([]) ((,) Prelude.String Prelude.String)) ->
                  Coq__UU03b1_CtxTrans
id_right_trans ren =
  list_rec Alpha_trans_nil (\a ren0 iHren ->
    case a of {
     (,) s s0 -> Alpha_trans_cons s s0 s0 ren0 (ctx_id_right ren0) ren0 iHren})
    ren

cons_split_helper :: Prelude.String -> Prelude.String -> (([])
                     ((,) Prelude.String Prelude.String)) -> (([])
                     ((,) Prelude.String Prelude.String)) -> (([])
                     ((,) Prelude.String Prelude.String)) -> Prelude.Either
                     (SigT (([]) ((,) Prelude.String Prelude.String)) ()) 
                     ()
cons_split_helper _ _ ren1 ren2 sigma =
  case ren1 of {
   ([]) -> Prelude.Right __;
   (:) _ l ->
    eq_rec_r (app l ren2)
      (eq_rec_r (app l ren2) (\_ -> Prelude.Left (ExistT l __)) sigma __)
      sigma}

shadow_helper_not_break :: Prelude.String -> Prelude.String -> Prelude.String
                           -> (([]) ((,) Prelude.String Prelude.String)) ->
                           NotBreakShadowing -> Prelude.Either () ()
shadow_helper_not_break z x y ren hshadow =
  case hshadow of {
   Not_break_shadow_nil x0 -> eq_rec_r z (\_ -> false_rec) x0 __;
   Not_break_shadow_cons z0 x0 x' ren0 x1 ->
    eq_rec_r z (\_ ->
      eq_rec_r x (\_ ->
        eq_rec_r y (\_ -> eq_rec_r ren (\_ _ _ -> Prelude.Right __) ren0) x')
        x0 __ __) z0 __ __ __ x1;
   Not_break_shadow_id z0 ren0 ->
    eq_rec_r z (\_ ->
      eq_rec_r x (\_ ->
        eq_rec_r y (\_ ->
          eq_rec_r ren
            (eq_rec_r x (\hshadow0 ->
              eq_rec_r y (\_ -> Prelude.Left __) x hshadow0) z hshadow) ren0)
          x) z __ __) z0 __}

alphavar_extend_id_split :: Prelude.String -> Prelude.String ->
                            Prelude.String -> (([])
                            ((,) Prelude.String Prelude.String)) -> AlphaVar
                            -> (([]) ((,) Prelude.String Prelude.String)) ->
                            (([]) ((,) Prelude.String Prelude.String)) ->
                            NotBreakShadowing -> AlphaVar
alphavar_extend_id_split x y z ren halpha ren1 ren2 x0 =
  alphaVar_rec (\x1 ren3 ren4 _ hshadow ->
    eq_rec_r ([]) (\_ ->
      eq_rec_r ([]) (\_ _ ->
        let {
         _evar_0_ = let {
                     _evar_0_ = let {
                                 b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                       x1 z}
                                in
                                case b of {
                                 Prelude.True ->
                                  eq_rec_r z (Alpha_var_cons z z ([])) x1;
                                 Prelude.False -> Alpha_var_diff z z x1 x1
                                  ([]) (Alpha_var_refl x1)}}
                    in
                    eq_rec_r ((:) ((,) z z) ([])) _evar_0_
                      (app ((:) ((,) z z) ([])) ([]))}
        in
        eq_rec_r (app ((:) ((,) z z) ([])) ([])) _evar_0_
          (app ([]) (app ((:) ((,) z z) ([])) ([])))) ren4 __ hshadow) ren3
      __) (\z0 w sigma ren3 ren4 _ hshadow ->
    let {hrenAdd = cons_split_helper z0 w ren3 ren4 sigma} in
    case hrenAdd of {
     Prelude.Left s ->
      case s of {
       ExistT x1 _ ->
        eq_rec_r ((:) ((,) z0 w) x1) (\_ -> Alpha_var_cons z0 w
          (let {
            app0 l m =
              case l of {
               ([]) -> m;
               (:) a l1 -> (:) a (app0 l1 m)}}
           in app0 x1 (app ((:) ((,) z z) ([])) ren4))) ren3 __};
     Prelude.Right _ ->
      eq_rec_r ([]) (\_ ->
        eq_rec_r ((:) ((,) z0 w) sigma) (\hshadow0 _ ->
          let {
           _evar_0_ = let {
                       hshadow1 = shadow_helper_not_break z z0 w sigma
                                    hshadow0}
                      in
                      case hshadow1 of {
                       Prelude.Left _ ->
                        eq_rec_r z0 (\_ ->
                          eq_rec_r w (\_ -> Alpha_var_cons w w ((:) ((,) w w)
                            sigma)) z0 __) z __;
                       Prelude.Right _ -> Alpha_var_diff z z z0 w ((:) ((,)
                        z0 w) sigma) (Alpha_var_cons z0 w sigma)}}
          in
          eq_rec_r (app ((:) ((,) z z) ([])) ((:) ((,) z0 w) sigma)) _evar_0_
            (app ([]) (app ((:) ((,) z z) ([])) ((:) ((,) z0 w) sigma))))
          ren4 hshadow __) ren3 __})
    (\x1 y0 z0 w sigma _ _ halpha0 iHHalpha ren3 ren4 _ hshadow ->
    let {hrenAdd = cons_split_helper x1 y0 ren3 ren4 sigma} in
    case hrenAdd of {
     Prelude.Left s ->
      case s of {
       ExistT x2 _ ->
        eq_rec_r ((:) ((,) x1 y0) x2) (\_ -> Alpha_var_diff x1 y0 z0 w
          (let {
            app0 l m =
              case l of {
               ([]) -> m;
               (:) a l1 -> (:) a (app0 l1 m)}}
           in app0 x2 (app ((:) ((,) z z) ([])) ren4))
          (iHHalpha x2 ren4 __ hshadow)) ren3 __};
     Prelude.Right _ ->
      eq_rec_r ([]) (\_ ->
        eq_rec_r ((:) ((,) x1 y0) sigma) (\hshadow0 _ ->
          let {
           _evar_0_ = let {
                       b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                             z z0}
                      in
                      case b of {
                       Prelude.True ->
                        let {
                         b0 = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                z w}
                        in
                        case b0 of {
                         Prelude.True ->
                          eq_rec_r z0 (\iHHalpha0 hshadow1 _ ->
                            eq_rec_r w (\_ _ _ _ -> Alpha_var_cons w w ((:)
                              ((,) x1 y0) sigma)) z0 __ halpha0 iHHalpha0
                              hshadow1) z iHHalpha hshadow0 __;
                         Prelude.False ->
                          eq_rec_r z0 (\_ _ _ -> false_rec) z iHHalpha
                            hshadow0 __};
                       Prelude.False ->
                        let {
                         b0 = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                z w}
                        in
                        case b0 of {
                         Prelude.True -> false_rec;
                         Prelude.False -> Alpha_var_diff z z z0 w ((:) ((,)
                          x1 y0) sigma) (Alpha_var_diff x1 y0 z0 w sigma
                          halpha0)}}}
          in
          eq_rec_r (app ((:) ((,) z z) ([])) ((:) ((,) x1 y0) sigma))
            _evar_0_
            (app ([]) (app ((:) ((,) z z) ([])) ((:) ((,) x1 y0) sigma))))
          ren4 hshadow __) ren3 __}) ren x y halpha ren1 ren2 __ x0

alpha_extend_id_split :: Term0 -> Term0 -> Prelude.String -> (([])
                         ((,) Prelude.String Prelude.String)) -> Alpha ->
                         (([]) ((,) Prelude.String Prelude.String)) -> (([])
                         ((,) Prelude.String Prelude.String)) ->
                         NotBreakShadowing -> Alpha
alpha_extend_id_split s t z ren halpha ren1 ren2 x =
  alpha_rec (\x0 y sigma a ren3 ren4 _ hshadow -> Alpha_var x0 y
    (app ren3 (app ((:) ((,) z z) ([])) ren4))
    (alphavar_extend_id_split x0 y z sigma a ren3 ren4 hshadow))
    (\b x0 y a s1 s2 _ _ iHHalpha ren3 ren4 _ hshadow -> Alpha_lam b x0 y a
    s1 s2 (app ren3 (app ((:) ((,) z z) ([])) ren4))
    (iHHalpha ((:) ((,) x0 y) ren3) ren4 __ hshadow))
    (\b s1 s2 t1 t2 _ _ iHHalpha1 _ iHHalpha2 ren3 ren4 _ hshadow ->
    Alpha_app b s1 s2 t1 t2 (app ren3 (app ((:) ((,) z z) ([])) ren4))
    (iHHalpha1 ren3 ren4 __ hshadow) (iHHalpha2 ren3 ren4 __ hshadow))
    (\_ d ren3 ren4 _ _ -> Alpha_builtin
    (app ren3 (app ((:) ((,) z z) ([])) ren4)) d) ren s t halpha ren1 ren2 __
    x

alpha_extend_ids_right :: Term0 -> Term0 -> (([])
                          ((,) Prelude.String Prelude.String)) -> (([])
                          ((,) Prelude.String Prelude.String)) -> IdCtx ->
                          Alpha -> Alpha
alpha_extend_ids_right s t ren idCtx hid halpha =
  idCtx_rec (eq_rec_r ren halpha (app ren ([]))) (\x ren0 hid0 iHHid ->
    let {
     _evar_0_ = alpha_extend_id_split s t x (app ren ren0) iHHid ren ren0
                  (idCtxNotBreakShadowing x ren0 hid0)}
    in
    eq_rec_r (app ren (app ((:) ((,) x x) ([])) ren0)) _evar_0_
      (app ren ((:) ((,) x x) ren0))) idCtx hid

alphavar_extend_ids_right :: Prelude.String -> Prelude.String -> (([])
                             ((,) Prelude.String Prelude.String)) -> (([])
                             ((,) Prelude.String Prelude.String)) -> IdCtx ->
                             AlphaVar -> AlphaVar
alphavar_extend_ids_right s t ren idCtx hid ha =
  let {
   h = alpha_extend_ids_right (Tmvar s) (Tmvar t) ren idCtx hid (Alpha_var s
         t ren ha)}
  in
  case h of {
   Alpha_var x y sigma x0 ->
    eq_rec_r (app ren idCtx) (\_ ->
      eq_rec_r s (\_ -> eq_rec_r t (\h3 -> h3) y) x) sigma __ __ x0;
   Alpha_lam _ _ _ _ _ _ sigma x ->
    eq_rec_r (app ren idCtx) (\_ -> false_rec) sigma __ __ x;
   Alpha_app _ _ _ _ _ sigma x x0 ->
    eq_rec_r (app ren idCtx) (\_ -> false_rec) sigma __ __ x x0;
   Alpha_builtin r _ -> eq_rec_r (app ren idCtx) (\_ -> false_rec) r __ __}

alphavar_extend_ids :: (([]) ((,) Prelude.String Prelude.String)) ->
                       Prelude.String -> Prelude.String -> IdCtx -> AlphaVar
                       -> AlphaVar
alphavar_extend_ids idCtx s t hid hav =
  case hav of {
   Alpha_var_refl x ->
    eq_rec_r s (\_ ->
      eq_rec_r t
        (eq_rec_r t (\hav0 ->
          idCtx_rec hav0 (\x0 ren _ iHHid ->
            let {
             b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                   x0 t}
            in
            case b of {
             Prelude.True -> eq_rec_r t (Alpha_var_cons t t ren) x0;
             Prelude.False -> Alpha_var_diff x0 x0 t t ren iHHid}) idCtx hid)
          s hav) s) x __;
   Alpha_var_cons _ _ _ -> false_rec __ __;
   Alpha_var_diff _ _ _ _ _ x -> false_rec __ __ __ __ x}

alpha_extend_ids :: (([]) ((,) Prelude.String Prelude.String)) -> Term0 ->
                    Term0 -> IdCtx -> Alpha -> Alpha
alpha_extend_ids idCtx s t =
  alpha_extend_ids_right s t ([]) idCtx

alphavar_lookup_helper :: (([]) ((,) Prelude.String Prelude.String)) ->
                          Prelude.String -> Prelude.String -> AlphaVar ->
                          Prelude.Either () ()
alphavar_lookup_helper r s s' x =
  alphaVar_rec (\_ -> Prelude.Right __) (\_ _ _ -> Prelude.Left __)
    (\_ _ _ _ _ _ _ _ iHAlphaVar ->
    case iHAlphaVar of {
     Prelude.Left _ -> Prelude.Left __;
     Prelude.Right _ -> Prelude.Right __}) r s s' x

lookup_some_IdCtx_then_alphavar :: (([]) ((,) Prelude.String Prelude.String))
                                   -> Prelude.String -> Prelude.String ->
                                   IdCtx -> AlphaVar
lookup_some_IdCtx_then_alphavar r s s' hid =
  list_rec (\_ _ -> false_rec) (\a r0 iHR hid0 _ ->
    case a of {
     (,) s0 s1 ->
      case hid0 of {
       Id_ctx_nil -> false_rec;
       Id_ctx_cons x ren x0 ->
        eq_rec_r s0 (\_ ->
          eq_rec_r s1 (\_ ->
            eq_rec_r r0 (\h0 ->
              eq_rec_r s1 (\hid1 _ ->
                let {
                 b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                       s1 s}
                in
                case b of {
                 Prelude.True ->
                  eq_rec_r s (\_ hid2 _ ->
                    eq_rec_r s'
                      (eq_rec_r s' (\_ _ _ _ -> Alpha_var_cons s' s' r0) s
                        hid2 __ iHR __) s) s1 __ hid1 __;
                 Prelude.False -> Alpha_var_diff s1 s1 s s' r0 (iHR h0 __)})
                s0 hid0 __) ren) s0) x __ __ x0}}) r hid __

lookup_some_then_alphavar :: (([]) ((,) Prelude.String Prelude.String)) ->
                             Prelude.String -> Prelude.String -> AlphaVar
lookup_some_then_alphavar r s s' =
  list_rec (\_ _ -> false_rec) (\a r0 iHR _ _ ->
    case a of {
     (,) s0 s1 ->
      let {
       b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             s0 s}
      in
      case b of {
       Prelude.True ->
        eq_rec_r s (\_ _ ->
          let {_evar_0_ = \_ -> eq_rec_r s' (Alpha_var_cons s s' r0) s1} in
          eq_rec_r Prelude.True _evar_0_
            (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
              s s) __) s0 __ __;
       Prelude.False -> Alpha_var_diff s0 s1 s s' r0 (iHR __ __)}}) r __ __

lookup_none_then_alpharefl :: (([]) ((,) Prelude.String Prelude.String)) ->
                              Prelude.String -> AlphaVar
lookup_none_then_alpharefl r s =
  list_rec (\_ _ -> Alpha_var_refl s) (\a r0 iHR _ _ ->
    case a of {
     (,) s0 s1 -> Alpha_var_diff s0 s1 s s r0 (iHR __ __)}) r __ __

alphavar_weaken_id :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
                      ((,) Prelude.String Prelude.String)) -> Prelude.String
                      -> Prelude.String -> Prelude.String -> IdCtx ->
                      AlphaVar -> AlphaVar
alphavar_weaken_id r idCtx1 s t x hid ha =
  let {ha0 = alphavar_lookup_helper (app r ((:) ((,) x x) idCtx1)) s t ha} in
  case ha0 of {
   Prelude.Left _ ->
    let {s0 = lookup_split_app_helper r ((:) ((,) x x) idCtx1) s t} in
    case s0 of {
     Prelude.Left _ -> lookup_some_then_alphavar (app r idCtx1) s t;
     Prelude.Right _ ->
      eq_rec_r s (\_ _ _ _ _ ->
        let {
         s1 = in_dec
                ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                s (map fst idCtx1)}
        in
        case s1 of {
         Prelude.True ->
          case hid of {
           Id_ctx_nil -> false_rec;
           Id_ctx_cons x0 ren x1 ->
            eq_rec_r x (\_ ->
              eq_rec_r x (\_ ->
                eq_rec_r idCtx1 (\_ ->
                  lookup_some_then_alphavar (app r idCtx1) s s) ren) x) x0 __
              __ x1};
         Prelude.False ->
          case hid of {
           Id_ctx_nil -> false_rec;
           Id_ctx_cons x0 ren x1 ->
            eq_rec_r x (\_ ->
              eq_rec_r x (\_ ->
                eq_rec_r idCtx1 (\_ ->
                  lookup_none_then_alpharefl (app r idCtx1) s) ren) x) x0 __
              __ x1}}) t __ __ __ __ __};
   Prelude.Right _ ->
    eq_rec_r t (\_ -> lookup_none_then_alpharefl (app r idCtx1) t) s __}

alpha_weaken_id :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
                   ((,) Prelude.String Prelude.String)) -> Term0 -> Term0 ->
                   Prelude.String -> Prelude.String -> IdCtx -> Alpha ->
                   Alpha
alpha_weaken_id r idCtx1 s t x y x0 x1 =
  eq_rec_r y (\h h0 ->
    let {gen_x = app r ((:) ((,) y y) idCtx1)} in
    alpha_rec (\x2 y0 sigma a r0 idCtx2 y1 _ ->
      solution_left (app r0 ((:) ((,) y1 y1) idCtx2)) (\a0 h1 -> Alpha_var x2
        y0 (app r0 idCtx2) (alphavar_weaken_id r0 idCtx2 x2 y0 y1 h1 a0))
        sigma a) (\b x2 y0 a s1 s2 sigma h1 iHAlpha r0 idCtx2 y1 _ ->
      solution_left (app r0 ((:) ((,) y1 y1) idCtx2)) (\_ iHAlpha0 h2 ->
        Alpha_lam b x2 y0 a s1 s2 (app r0 idCtx2)
        (iHAlpha0 ((:) ((,) x2 y0) r0) idCtx2 y1 __ h2)) sigma h1 iHAlpha)
      (\b s1 s2 t1 t2 sigma h0_ iHAlpha1 h0_0 iHAlpha2 r0 idCtx2 y0 _ ->
      solution_left (app r0 ((:) ((,) y0 y0) idCtx2))
        (\_ _ iHAlpha3 iHAlpha4 h1 -> Alpha_app b s1 s2 t1 t2 (app r0 idCtx2)
        (iHAlpha3 r0 idCtx2 y0 __ h1) (iHAlpha4 r0 idCtx2 y0 __ h1)) sigma
        h0_ h0_0 iHAlpha1 iHAlpha2) (\r0 d r1 idCtx2 y0 _ ->
      solution_left (app r1 ((:) ((,) y0 y0) idCtx2)) (\d0 _ -> Alpha_builtin
        (app r1 idCtx2) d0) r0 d) gen_x s t h0 r idCtx1 y __ h) x x0 x1

alpha_weaken_ids :: (([]) ((,) Prelude.String Prelude.String)) -> Term0 ->
                    Term0 -> IdCtx -> Alpha -> Alpha
alpha_weaken_ids idCtx s t hid hav =
  list_rec (\_ hav0 -> hav0) (\a idCtx0 iHidCtx hid0 hav0 ->
    iHidCtx
      (case hid0 of {
        Id_ctx_nil -> false_rec;
        Id_ctx_cons _ ren x -> eq_rec_r idCtx0 (\h0 -> h0) ren x})
      (case a of {
        (,) s0 s1 ->
         let {_evar_0_ = alpha_weaken_id ([]) idCtx0 s t s0 s1 hid0 hav0} in
         eq_rec_r (app ([]) idCtx0) _evar_0_ idCtx0})) idCtx hid hav

alpha_extend_id' :: Term0 -> Term0 -> Prelude.String -> (([])
                    ((,) Prelude.String Prelude.String)) -> Alpha ->
                    NotBreakShadowing -> Alpha
alpha_extend_id' s t z ren halpha hren =
  alpha_extend_id_split s t z ren halpha ([]) ren hren

alpha_extend_id :: Term0 -> Prelude.String -> (([])
                   ((,) Prelude.String Prelude.String)) -> NotBreakShadowing
                   -> Alpha -> Alpha
alpha_extend_id s z ren hren halpha =
  alpha_extend_id' s s z ren halpha hren

alpha_extend_vacuous :: Prelude.String -> Prelude.String -> Term0 -> Term0 ->
                        (([]) ((,) Prelude.String Prelude.String)) -> Alpha
                        -> Alpha
alpha_extend_vacuous x x' s s' r ha_s =
  alpha_rec (\x0 y sigma a _ _ -> Alpha_var x0 y ((:) ((,) x x') sigma)
    (Alpha_var_diff x x' x0 y sigma a))
    (\b x0 y a s1 s2 sigma _ iHHa_s _ _ -> Alpha_lam b x0 y a s1 s2 ((:) ((,)
    x x') sigma)
    (alpha_swap s1 s2 ((:) ((,) x0 y) ((:) ((,) x x') sigma)) ((:) ((,) x x')
      ((:) ((,) x0 y) sigma)) (Lrs_start x x' x0 y sigma sigma
      (legalRenSwap_id sigma)) (iHHa_s __ __)))
    (\b s1 s2 t1 t2 sigma _ iHHa_s1 _ iHHa_s2 _ _ -> Alpha_app b s1 s2 t1 t2
    ((:) ((,) x x') sigma) (iHHa_s1 __ __) (iHHa_s2 __ __)) (\r0 d _ _ ->
    Alpha_builtin ((:) ((,) x x') r0) d) r s s' ha_s __ __

alphavar_refl_weaken_vacuouss :: Prelude.String -> (([])
                                 ((,) Prelude.String Prelude.String)) ->
                                 AlphaVar
alphavar_refl_weaken_vacuouss x r =
  list_rec (\_ _ -> Alpha_var_refl x) (\a r0 iHR _ _ ->
    case a of {
     (,) s s0 -> Alpha_var_diff s s0 x x r0 (iHR __ __)}) r __ __

alphaIdShadowsVacuous :: Prelude.String -> Prelude.String -> Term0 -> Alpha
alphaIdShadowsVacuous x x' s =
  term_rec (\s0 _ -> Alpha_var s0 s0 ((:) ((,) x x) ((:) ((,) x x') ([])))
    (let {
      b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
            x s0}
     in
     case b of {
      Prelude.True ->
       eq_rec_r s0 (Alpha_var_cons s0 s0 ((:) ((,) s0 x') ([]))) x;
      Prelude.False -> Alpha_var_diff x x s0 s0 ((:) ((,) x x') ([]))
       (Alpha_var_diff x x' s0 s0 ([]) (Alpha_var_refl s0))}))
    (\uSort s0 k s1 iHs _ -> Alpha_lam uSort s0 s0 k s1 s1 ((:) ((,) x x)
    ((:) ((,) x x') ([])))
    (let {
      b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
            x' x}
     in
     case b of {
      Prelude.True ->
       eq_rec_r x (\_ _ iHs0 ->
         let {
          b0 = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 x s0}
         in
         case b0 of {
          Prelude.True ->
           eq_rec_r s0 (\iHs1 _ _ ->
             alpha_extend_id s1 s0 ((:) ((,) s0 s0) ((:) ((,) s0 s0) ([])))
               (Not_break_shadow_cons s0 s0 s0 ((:) ((,) s0 s0) ([]))
               (Not_break_shadow_cons s0 s0 s0 ([]) (Not_break_shadow_nil
               s0))) (iHs1 __)) x iHs0 __ __;
          Prelude.False ->
           alpha_extend_id s1 s0 ((:) ((,) x x) ((:) ((,) x x) ([])))
             (Not_break_shadow_cons s0 x x ((:) ((,) x x) ([]))
             (Not_break_shadow_cons s0 x x ([]) (Not_break_shadow_nil s0)))
             (iHs0 __)}) x' __ __ iHs;
      Prelude.False ->
       let {
        b0 = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
               x s0}
       in
       case b0 of {
        Prelude.True ->
         eq_rec_r s0 (\iHs0 _ ->
           alpha_extend_id s1 s0 ((:) ((,) s0 s0) ((:) ((,) s0 x') ([])))
             (Not_break_shadow_id s0 ((:) ((,) s0 x') ([]))) (iHs0 __)) x iHs
           __;
        Prelude.False ->
         alpha_extend_id s1 s0 ((:) ((,) x x) ((:) ((,) x x') ([])))
           (Not_break_shadow_cons s0 x x ((:) ((,) x x') ([]))
           (Not_break_shadow_cons s0 x x' ([]) (Not_break_shadow_nil s0)))
           (iHs __)}})) (\bSort s1 iHs1 s2 iHs2 _ -> Alpha_app bSort s1 s1 s2
    s2 ((:) ((,) x x) ((:) ((,) x x') ([]))) (iHs1 __) (iHs2 __)) (\d _ ->
    Alpha_builtin ((:) ((,) x x) ((:) ((,) x x') ([]))) d) s __

alpha_trans3 :: (([]) ((,) Prelude.String Prelude.String)) -> Term0 -> Term0
                -> Term0 -> Term0 -> Alpha -> Alpha -> Alpha -> Alpha
alpha_trans3 r s s' s'' s''' x x0 x1 =
  alpha_trans s s' s''' (ctx_id_left r) r r (id_left_trans r)
    (alpha_extend_ids (ctx_id_left r) s s' (ctx_id_left_is_id r) x)
    (alpha_trans s' s'' s''' r (ctx_id_right r) r (id_right_trans r) x0
      (alpha_extend_ids (ctx_id_right r) s'' s''' (ctx_id_right_is_id r) x1))

data Coq__UU03b1_CtxSub =
   Alpha_ctx_nil (([]) ((,) Prelude.String Prelude.String))
 | Alpha_ctx_cons (([]) ((,) Prelude.String Prelude.String)) (([])
                                                             ((,)
                                                             Prelude.String
                                                             Term0)) 
 (([]) ((,) Prelude.String Term0)) Prelude.String Prelude.String Term0 
 Term0 Coq__UU03b1_CtxSub AlphaVar Alpha

_UU03b1_CtxSub_rect :: ((([]) ((,) Prelude.String Prelude.String)) -> a1) ->
                       ((([]) ((,) Prelude.String Prelude.String)) -> (([])
                       ((,) Prelude.String Term0)) -> (([])
                       ((,) Prelude.String Term0)) -> Prelude.String ->
                       Prelude.String -> Term0 -> Term0 -> Coq__UU03b1_CtxSub
                       -> a1 -> AlphaVar -> Alpha -> a1) -> (([])
                       ((,) Prelude.String Prelude.String)) -> (([])
                       ((,) Prelude.String Term0)) -> (([])
                       ((,) Prelude.String Term0)) -> Coq__UU03b1_CtxSub ->
                       a1
_UU03b1_CtxSub_rect f0 f1 _ _ _ _UU03b1_ =
  case _UU03b1_ of {
   Alpha_ctx_nil r -> f0 r;
   Alpha_ctx_cons r _UU03c3_ _UU03c3_' x y t t' _UU03b1_0 a a0 ->
    f1 r _UU03c3_ _UU03c3_' x y t t' _UU03b1_0
      (_UU03b1_CtxSub_rect f0 f1 r _UU03c3_ _UU03c3_' _UU03b1_0) a a0}

_UU03b1_CtxSub_rec :: ((([]) ((,) Prelude.String Prelude.String)) -> a1) ->
                      ((([]) ((,) Prelude.String Prelude.String)) -> (([])
                      ((,) Prelude.String Term0)) -> (([])
                      ((,) Prelude.String Term0)) -> Prelude.String ->
                      Prelude.String -> Term0 -> Term0 -> Coq__UU03b1_CtxSub
                      -> a1 -> AlphaVar -> Alpha -> a1) -> (([])
                      ((,) Prelude.String Prelude.String)) -> (([])
                      ((,) Prelude.String Term0)) -> (([])
                      ((,) Prelude.String Term0)) -> Coq__UU03b1_CtxSub -> a1
_UU03b1_CtxSub_rec =
  _UU03b1_CtxSub_rect

alpha_ctx_right_ex :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
                      ((,) Prelude.String Term0)) -> (([])
                      ((,) Prelude.String Term0)) -> Prelude.String ->
                      Prelude.String -> Term0 -> Coq__UU03b1_CtxSub ->
                      AlphaVar -> SigT Term0 ((,) () Alpha)
alpha_ctx_right_ex ren sigma sigma' x x' t x0 x1 =
  _UU03b1_CtxSub_rec (\_ _ _ -> false_rec)
    (\_ _ _ x2 y t0 t' _ iH_UU03b1_CtxSub a a0 h0 _ ->
    let {
     b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           x2 x}
    in
    case b of {
     Prelude.True ->
      eq_rec_r x (\a1 _ ->
        eq_rec_r t
          (eq_rec_r t (\a2 _ _ ->
            eq_rec_r x' (\_ -> ExistT t' ((,) __ a2)) y a1) t0 a0 __ __) t0)
        x2 a __;
     Prelude.False ->
      let {
       _evar_0_ = \_ ->
        let {h4 = iH_UU03b1_CtxSub h0 __} in
        case h4 of {
         ExistT x3 p -> case p of {
                         (,) _ a1 -> ExistT x3 ((,) __ a1)}}}
      in
      eq_rec_r Prelude.False _evar_0_
        (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
          x2 x) __}) ren sigma sigma' x0 x1 __

alpha_ctx_ren_nil :: (([]) ((,) Prelude.String Term0)) -> Coq__UU03b1_CtxSub
alpha_ctx_ren_nil sigma =
  list_rec (Alpha_ctx_nil ([])) (\a sigma0 iHsigma ->
    case a of {
     (,) s t -> Alpha_ctx_cons ([]) sigma0 sigma0 s s t t iHsigma
      (Alpha_var_refl s) (alpha_refl t ([]) Alpha_refl_nil)}) sigma

_UU03b1_ctx_trans :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
                     ((,) Prelude.String Prelude.String)) -> (([])
                     ((,) Prelude.String Prelude.String)) -> (([])
                     ((,) Prelude.String Term0)) -> (([])
                     ((,) Prelude.String Term0)) -> (([])
                     ((,) Prelude.String Term0)) -> Coq__UU03b1_CtxTrans ->
                     Coq__UU03b1_CtxSub -> Coq__UU03b1_CtxSub ->
                     Coq__UU03b1_CtxSub
_UU03b1_ctx_trans r1 r2 r _UU03c3_ _UU03c3_' _UU03c3_'' x x0 x1 =
  list_rec (\_ _ _ h0 h1 ->
    case h0 of {
     Alpha_ctx_nil r0 ->
      eq_rec_r r1 (\_ _ ->
        case h1 of {
         Alpha_ctx_nil r3 -> eq_rec_r r2 (\_ _ -> Alpha_ctx_nil r) r3 __ __;
         Alpha_ctx_cons r3 _ _ _ _ _ _ x2 x3 x4 ->
          eq_rec_r r2 (\_ -> false_rec) r3 __ __ x2 x3 x4}) r0 __ __;
     Alpha_ctx_cons r0 _ _ _ _ _ _ x2 x3 x4 ->
      eq_rec_r r1 (\_ -> false_rec) r0 __ __ x2 x3 x4})
    (\_ _UU03c3_0 iH_UU03c3_ _ _ h h0 h1 ->
    case h0 of {
     Alpha_ctx_nil r0 -> eq_rec_r r1 (\_ -> false_rec) r0 __ __;
     Alpha_ctx_cons r0 _UU03c3_1 _UU03c3_'0 x2 y t t' x3 x4 x5 ->
      eq_rec_r r1 (\_ ->
        eq_rec_r _UU03c3_0 (\_ h4 h6 h8 ->
          case h1 of {
           Alpha_ctx_nil r3 -> eq_rec_r r2 (\_ -> false_rec) r3 __ __;
           Alpha_ctx_cons r3 _UU03c3_2 _UU03c3_'1 x6 y0 t0 t'0 x7 x8 x9 ->
            eq_rec_r r2 (\_ ->
              eq_rec_r y (\_ ->
                eq_rec_r t' (\_ ->
                  eq_rec_r _UU03c3_'0 (\_ h9 h11 h12 -> Alpha_ctx_cons r
                    _UU03c3_0 _UU03c3_'1 x2 y0 t t'0
                    (iH_UU03c3_ _UU03c3_'0 _UU03c3_'1 h h4 h9)
                    (alpha_var_trans x2 y y0 r1 r2 r h h6 h11)
                    (alpha_trans t t' t'0 r1 r2 r h h8 h12)) _UU03c3_2) t0)
                x6 __ __) r3 __ __ x7 x8 x9}) _UU03c3_1) r0 __ __ x3 x4 x5})
    _UU03c3_ _UU03c3_' _UU03c3_'' x x0 x1

_UU03b1_ctx_sub_extend_ids_right :: (([]) ((,) Prelude.String Term0)) ->
                                    (([]) ((,) Prelude.String Term0)) ->
                                    (([])
                                    ((,) Prelude.String Prelude.String)) ->
                                    (([])
                                    ((,) Prelude.String Prelude.String)) ->
                                    IdCtx -> Coq__UU03b1_CtxSub ->
                                    Coq__UU03b1_CtxSub
_UU03b1_ctx_sub_extend_ids_right _UU03c3_ _UU03c3_' r1 r2 hidR2 ha =
  list_rec (\_ r3 r4 _ ha0 ->
    case ha0 of {
     Alpha_ctx_nil r ->
      eq_rec_r r3 (\_ _ -> Alpha_ctx_nil (app r3 r4)) r __ __;
     Alpha_ctx_cons r _ _ _ _ _ _ x x0 x1 ->
      eq_rec_r r3 (\_ -> false_rec) r __ __ x x0 x1})
    (\_ _UU03c3_0 iH_UU03c3_ _ r3 r4 hidR3 ha0 ->
    case ha0 of {
     Alpha_ctx_nil r -> eq_rec_r r3 (\_ -> false_rec) r __ __;
     Alpha_ctx_cons r _UU03c3_1 _UU03c3_'0 x y t t' x0 x1 x2 ->
      eq_rec_r r3 (\_ ->
        eq_rec_r _UU03c3_0 (\_ h1 h3 h5 -> Alpha_ctx_cons (app r3 r4)
          _UU03c3_0 _UU03c3_'0 x y t t'
          (iH_UU03c3_ _UU03c3_'0 r3 r4 hidR3 h1)
          (alphavar_extend_ids_right x y r3 r4 hidR3 h3)
          (alpha_extend_ids_right t t' r3 r4 hidR3 h5)) _UU03c3_1) r __ __ x0
        x1 x2}) _UU03c3_ _UU03c3_' r1 r2 hidR2 ha

alphaRename :: Prelude.String -> Prelude.String -> Term0 -> Alpha
alphaRename x x' s =
  term_rec (\s0 _ ->
    let {
     b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
           s0}
    in
    case b of {
     Prelude.True ->
      eq_rec_r s0 (Alpha_var s0 x' ((:) ((,) s0 x') ([])) (Alpha_var_cons s0
        x' ([]))) x;
     Prelude.False -> Alpha_var s0 s0 ((:) ((,) x x') ([])) (Alpha_var_diff x
      x' s0 s0 ([]) (Alpha_var_refl s0))}) (\uSort s0 k s1 iHs _ ->
    let {
     b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           s0 x}
    in
    case b of {
     Prelude.True ->
      eq_rec_r x (\_ ->
        eq_rec_r (Tmabs uSort x k s1) (Alpha_lam uSort x x k s1 s1 ((:) ((,)
          x x') ([])) (alphaIdShadowsVacuous x x' s1))
          (rename0 x x' (Tmabs uSort x k s1))) s0 __;
     Prelude.False ->
      eq_rec_r (Tmabs uSort s0 k (rename0 x x' s1)) (Alpha_lam uSort s0 s0 k
        s1 (rename0 x x' s1) ((:) ((,) x x') ([]))
        (alpha_extend_id' s1 (rename0 x x' s1) s0 ((:) ((,) x x') ([]))
          (iHs __) (Not_break_shadow_cons s0 x x' ([]) (Not_break_shadow_nil
          s0)))) (rename0 x x' (Tmabs uSort s0 k s1))})
    (\bSort s1 iHs1 s2 iHs2 _ -> Alpha_app bSort s1
    (let {
      rename1 x0 x'0 t =
        case t of {
         Tmvar y ->
          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 x0 y of {
           Prelude.True -> Tmvar x'0;
           Prelude.False -> Tmvar y};
         Tmabs b y k1 t_body ->
          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 x0 y of {
           Prelude.True -> Tmabs b y k1 t_body;
           Prelude.False -> Tmabs b y k1 (rename1 x0 x'0 t_body)};
         Tmbin b t1 t2 -> Tmbin b (rename1 x0 x'0 t1) (rename1 x0 x'0 t2);
         Tmbuiltin d -> Tmbuiltin d}}
     in rename1 x x' s1) s2
    (let {
      rename1 x0 x'0 t =
        case t of {
         Tmvar y ->
          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 x0 y of {
           Prelude.True -> Tmvar x'0;
           Prelude.False -> Tmvar y};
         Tmabs b y k1 t_body ->
          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 x0 y of {
           Prelude.True -> Tmabs b y k1 t_body;
           Prelude.False -> Tmabs b y k1 (rename1 x0 x'0 t_body)};
         Tmbin b t1 t2 -> Tmbin b (rename1 x0 x'0 t1) (rename1 x0 x'0 t2);
         Tmbuiltin d -> Tmbuiltin d}}
     in rename1 x x' s2) ((:) ((,) x x') ([])) (iHs1 __) (iHs2 __)) (\d _ ->
    Alpha_builtin ((:) ((,) x x') ([])) d) s __

alpha_trans_rename_right :: Term0 -> Term0 -> Prelude.String ->
                            Prelude.String -> Prelude.String -> (([])
                            ((,) Prelude.String Prelude.String)) -> (([])
                            ((,) Prelude.String Term0)) -> Alpha -> Alpha
alpha_trans_rename_right u v b'' s'' s ren _ x =
  alpha_trans u v (rename0 s'' b'' v) ((:) ((,) s s'') ren)
    (app ((:) ((,) s'' b'') ([])) (ctx_id_right ren)) ((:) ((,) s b'') ren)
    (Alpha_trans_cons s s'' b'' ren (ctx_id_right ren) ren
    (id_right_trans ren)) x
    (alpha_extend_ids_right v (rename0 s'' b'' v) ((:) ((,) s'' b'') ([]))
      (ctx_id_right ren) (ctx_id_right_is_id ren) (alphaRename s'' b'' v))

alpha_trans_rename_left :: Term0 -> Term0 -> Prelude.String -> Prelude.String
                           -> Prelude.String -> (([])
                           ((,) Prelude.String Prelude.String)) -> (([])
                           ((,) Prelude.String Term0)) -> Alpha -> Alpha
alpha_trans_rename_left u v b' s' s ren _ x =
  alpha_trans (rename0 s' b' u) u v
    (app ((:) ((,) b' s') ([])) (ctx_id_left ren)) ((:) ((,) s' s) ren) ((:)
    ((,) b' s) ren) (Alpha_trans_cons b' s' s (ctx_id_left ren) ren ren
    (id_left_trans ren))
    (alpha_extend_ids_right (rename0 s' b' u) u ((:) ((,) b' s') ([]))
      (ctx_id_left ren) (ctx_id_left_is_id ren)
      (alpha_sym u (rename0 s' b' u) ((:) ((,) s' b') ([])) ((:) ((,) b' s')
        ([])) (Alpha_sym_cons s' b' ([]) ([]) Alpha_sym_nil)
        (alphaRename s' b' u))) x

data GU =
   GU_var Prelude.String
 | GU_app BSort Term0 Term0 GU GU
 | GU_lam USort Prelude.String Kind Term0 GU
 | GU_builtin DefaultUni

data NC =
   Nc_nil Term0
 | Nc_cons Term0 Prelude.String Term0 (([]) ((,) Prelude.String Term0)) 
 NC

nc_lam :: USort -> Prelude.String -> Term0 -> Kind -> (([])
          ((,) Prelude.String Term0)) -> NC -> NC
nc_lam b x s a sigma =
  list_rec (\_ -> Nc_nil s) (\_ sigma0 iHsigma hnc ->
    case hnc of {
     Nc_nil s0 -> eq_rec_r (Tmabs b x a s) (\_ -> false_rec) s0 __;
     Nc_cons s0 x0 t sigma1 x1 ->
      eq_rec_r (Tmabs b x a s) (\_ ->
        eq_rec_r sigma0 (\h2 _ -> Nc_cons s x0 t sigma0 (iHsigma h2)) sigma1)
        s0 __ x1 __}) sigma

nc_app_l :: BSort -> Term0 -> Term0 -> (([]) ((,) Prelude.String Term0)) ->
            NC -> NC
nc_app_l b s t sigma =
  list_rec (\_ -> Nc_nil s) (\_ sigma0 iHsigma hnc ->
    case hnc of {
     Nc_nil s0 -> eq_rec_r (Tmbin b s t) (\_ -> false_rec) s0 __;
     Nc_cons s0 x t0 sigma1 x0 ->
      eq_rec_r (Tmbin b s t) (\_ ->
        eq_rec_r sigma0 (\h2 _ -> Nc_cons s x t0 sigma0 (iHsigma h2)) sigma1)
        s0 __ x0 __}) sigma

nc_app_r :: BSort -> Term0 -> Term0 -> (([]) ((,) Prelude.String Term0)) ->
            NC -> NC
nc_app_r b s t sigma =
  list_rec (\_ -> Nc_nil t) (\_ sigma0 iHsigma hnc ->
    case hnc of {
     Nc_nil s0 -> eq_rec_r (Tmbin b s t) (\_ -> false_rec) s0 __;
     Nc_cons s0 x t0 sigma1 x0 ->
      eq_rec_r (Tmbin b s t) (\_ ->
        eq_rec_r sigma0 (\h2 _ -> Nc_cons t x t0 sigma0 (iHsigma h2)) sigma1)
        s0 __ x0 __}) sigma

alpha_preserves_nc_ctx :: Term0 -> Prelude.String -> Term0 -> Term0 -> Alpha
                          -> NC -> NC
alpha_preserves_nc_ctx s x t t' _ hnc_t =
  case hnc_t of {
   Nc_nil s0 -> eq_rec_r s (\_ -> false_rec) s0 __;
   Nc_cons s0 x0 t0 sigma x1 ->
    eq_rec_r s (\_ ->
      eq_rec_r x (\_ ->
        eq_rec_r t (\_ ->
          eq_rec_r ([]) (\h2 _ -> Nc_cons s x t' ([]) h2) sigma) t0) x0 __ __)
      s0 __ x1 __}

gu_app_l :: BSort -> Term0 -> Term0 -> GU -> GU
gu_app_l b s t h =
  case h of {
   GU_app b0 s0 t0 x x0 ->
    eq_rec_r b (\_ -> eq_rec_r s (\_ -> eq_rec_r t (\h2 _ _ _ -> h2) t0) s0)
      b0 __ __ x x0 __ __;
   GU_lam _ _ _ _ x -> false_rec x __;
   _ -> false_rec}

gu_app_r :: BSort -> Term0 -> Term0 -> GU -> GU
gu_app_r b s t h =
  case h of {
   GU_app b0 s0 t0 x x0 ->
    eq_rec_r b (\_ -> eq_rec_r s (\_ -> eq_rec_r t (\_ h4 _ _ -> h4) t0) s0)
      b0 __ __ x x0 __ __;
   GU_lam _ _ _ _ x -> false_rec x __;
   _ -> false_rec}

gu_lam :: USort -> Prelude.String -> Kind -> Term0 -> GU -> GU
gu_lam b x a s h =
  case h of {
   GU_app _ _ _ x0 x1 -> false_rec x0 x1 __ __;
   GU_lam b0 x0 a0 s0 x1 ->
    eq_rec_r b (\_ ->
      eq_rec_r x (\_ -> eq_rec_r a (\_ -> eq_rec_r s (\h2 _ -> h2) s0) a0) x0)
      b0 __ __ __ x1 __;
   _ -> false_rec}

gu_app_st__gu_app_ts :: BSort -> Term0 -> Term0 -> GU -> GU
gu_app_st__gu_app_ts b s1 s2 x =
  case x of {
   GU_app b0 s t x0 x1 ->
    eq_rec_r b (\_ ->
      eq_rec_r s1 (\_ -> eq_rec_r s2 (\h2 h4 _ _ -> GU_app b s2 s1 h4 h2) t)
        s) b0 __ __ x0 x1 __ __;
   GU_lam _ _ _ _ x0 -> false_rec x0 __;
   _ -> false_rec}

gu_applam_to_nc :: BSort -> USort -> Term0 -> Term0 -> Prelude.String -> Kind
                   -> GU -> NC
gu_applam_to_nc bA bL s t x a hgu =
  case hgu of {
   GU_app b s0 t0 x0 x1 ->
    eq_rec_r bA (\_ ->
      eq_rec_r (Tmabs bL x a s) (\_ ->
        eq_rec_r t (\_ _ _ _ -> Nc_cons s x t ([]) (Nc_nil s)) t0) s0) b __
      __ x0 x1 __ __;
   GU_lam _ _ _ _ x0 -> false_rec x0 __;
   _ -> false_rec}

nc_helper :: Term0 -> (([]) ((,) Prelude.String Term0)) -> NC
nc_helper s sigma =
  list_rec (\_ -> Nc_nil s) (\a sigma0 iHsigma _ ->
    case a of {
     (,) s0 t -> Nc_cons s s0 t sigma0 (iHsigma __)}) sigma __

step_naive_preserves_nc_ctx :: Term0 -> Term0 -> Term0 -> Prelude.String ->
                               Step_naive -> NC -> NC
step_naive_preserves_nc_ctx s t1 t2 x _ hnc =
  case hnc of {
   Nc_nil s0 -> eq_rec_r s (\_ -> false_rec) s0 __;
   Nc_cons s0 x0 t sigma x1 ->
    eq_rec_r s (\_ ->
      eq_rec_r x (\_ ->
        eq_rec_r t1 (\_ ->
          eq_rec_r ([]) (\_ _ -> Nc_cons s x t2 ([]) (Nc_nil s)) sigma) t) x0
        __ __) s0 __ x1 __}

data InSet a =
   InSet_head (([]) a)
 | InSet_tail a (([]) a) (InSet a)

in_app_or_set :: a1 -> (([]) a1) -> (([]) a1) -> (InSet a1) -> Prelude.Either
                 (InSet a1) (InSet a1)
in_app_or_set _ l1 _ =
  list_rect (\h -> Prelude.Right h) (\h t iH h0 ->
    case h0 of {
     InSet_head _ -> Prelude.Left (InSet_head t);
     InSet_tail _ _ x ->
      let {s = iH x} in
      case s of {
       Prelude.Left i -> Prelude.Left (InSet_tail h t i);
       Prelude.Right i -> Prelude.Right i}}) l1

in_dec_f :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (([]) a1) -> Prelude.Bool
in_dec_f eq_dec x l =
  case l of {
   ([]) -> Prelude.False;
   (:) h hs ->
    case eq_dec x h of {
     Prelude.True -> Prelude.True;
     Prelude.False -> in_dec_f eq_dec x hs}}

in_dec_f_sound :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (([]) a1) -> InSet a1
in_dec_f_sound eq_dec x l =
  list_rect (\_ -> Prelude.error "absurd case") (\h t iH _ ->
    let {s = eq_dec x h} in
    case s of {
     Prelude.True -> InSet_head t;
     Prelude.False -> InSet_tail h t (iH __)}) l __

in_prop_to_set :: Prelude.String -> (([]) Prelude.String) -> InSet
                  Prelude.String
in_prop_to_set x l =
  let {
   b = in_dec_f
         ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
         l}
  in
  case b of {
   Prelude.True ->
    in_dec_f_sound
      ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x l;
   Prelude.False -> Prelude.error "absurd case"}

id_ctx_alphavar_refl :: (([]) ((,) Prelude.String Prelude.String)) ->
                        Prelude.String -> IdCtx -> AlphaVar
id_ctx_alphavar_refl r x x0 =
  let {
   h0 = alpha_extend_ids r (Tmvar x) (Tmvar x) x0
          (alpha_refl (Tmvar x) ([]) Alpha_refl_nil)}
  in
  case h0 of {
   Alpha_var x1 y sigma x2 ->
    eq_rec_r r (\_ -> eq_rec_r x (\_ -> eq_rec_r x (\h4 -> h4) y) x1) sigma
      __ __ x2;
   Alpha_lam _ _ _ _ _ _ sigma x1 ->
    eq_rec_r r (\_ -> false_rec) sigma __ __ x1;
   Alpha_app _ _ _ _ _ sigma x1 x2 ->
    eq_rec_r r (\_ -> false_rec) sigma __ __ x1 x2;
   Alpha_builtin r0 _ -> eq_rec_r r (\_ -> false_rec) r0 __ __}

fresh_to_GU_ :: (([]) Prelude.String) -> (([])
                ((,) Prelude.String Prelude.String)) -> Prelude.String ->
                Prelude.String
fresh_to_GU_ ftvs binders x =
  concat0 ""
    (app ftvs
      (app (map fst binders)
        (app (map snd binders) ((:) x (app ([]) ((:) "a" ([])))))))

to_GU_ :: (([]) Prelude.String) -> (([]) ((,) Prelude.String Prelude.String))
          -> Term0 -> (,)
          ((,) (([]) Prelude.String)
          (([]) ((,) Prelude.String Prelude.String))) Term0
to_GU_ used binders s =
  case s of {
   Tmvar x ->
    case lookup x binders of {
     Prelude.Just y -> (,) ((,) ((:) y used) binders) (Tmvar y);
     Prelude.Nothing -> (,) ((,) ((:) x used) binders) (Tmvar x)};
   Tmabs b x a s0 ->
    let {x' = fresh_to_GU_ used binders x} in
    case to_GU_ used ((:) ((,) x x') binders) s0 of {
     (,) acc term_body -> (,) ((,) (app (fst acc) ((:) x ((:) x' ([]))))
      binders) (Tmabs b x' a term_body)};
   Tmbin b s0 t ->
    case to_GU_ used binders s0 of {
     (,) acc_s s' ->
      case to_GU_ (fst acc_s) binders t of {
       (,) acc_t t' -> (,) acc_t (Tmbin b s' t')}};
   Tmbuiltin d -> (,) ((,) used binders) (Tmbuiltin d)}

to_GU :: Term0 -> Term0
to_GU s =
  let {tvs = tv s} in snd (to_GU_ tvs (map (\x -> (,) x x) tvs) s)

type KindOfUniqueRhs = Prelude.String -> Prelude.String -> () -> AlphaVar

kindOfUniqueRhsFresh :: Prelude.String -> (([])
                        ((,) Prelude.String Prelude.String)) -> (([])
                        ((,) Prelude.String Prelude.String)) -> (([])
                        Prelude.String) -> KindOfUniqueRhs -> Prelude.String
                        -> Prelude.String -> AlphaVar
kindOfUniqueRhsFresh x r r' used x0 x1 y =
  let {
   b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x1
         x}
  in
  case b of {
   Prelude.True ->
    eq_rec_r x (\_ ->
      let {_evar_0_ = \_ -> Alpha_var_cons x (fresh_to_GU_ used r' x) r} in
      eq_rec_r Prelude.True _evar_0_
        (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
          x) __) x1 __;
   Prelude.False ->
    let {
     _evar_0_ = \_ ->
      let {
       _evar_0_ = \_ -> Alpha_var_diff x (fresh_to_GU_ used r' x) x1 y r
        (x0 x1 y __)}
      in
      eq_rec_r Prelude.False _evar_0_
        (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
          x1) __}
    in
    eq_rec_r
      (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
        x1) _evar_0_
      (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x1
        x) __}

idCtx__KindOfUniqueRhs :: (([]) ((,) Prelude.String Prelude.String)) -> IdCtx
                          -> Prelude.String -> Prelude.String -> AlphaVar
idCtx__KindOfUniqueRhs r x x0 y =
  idCtx_rec (\_ -> false_rec) (\x1 ren _ iHIdCtx _ ->
    let {
     b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           x0 x1}
    in
    case b of {
     Prelude.True ->
      eq_rec_r x1 (\_ iHIdCtx0 ->
        let {
         _evar_0_ = \_ ->
          eq_rec_r y (eq_rec_r y (\_ -> Alpha_var_cons y y ren) x1 iHIdCtx0)
            x1}
        in
        eq_rec_r Prelude.True _evar_0_
          (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
            x1 x1) __) x0 __ iHIdCtx;
     Prelude.False ->
      let {
       _evar_0_ = \_ ->
        let {
         _evar_0_ = \_ ->
          let {iHIdCtx0 = iHIdCtx __} in
          eq_rec_r y (\_ _ iHIdCtx' -> Alpha_var_diff x1 x1 y y ren iHIdCtx')
            x0 __ __ iHIdCtx0}
        in
        eq_rec_r Prelude.False _evar_0_
          (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
            x1 x0) __}
      in
      eq_rec_r
        (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
          x1 x0) _evar_0_
        (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
          x0 x1) __}) r x __

to_GU__alpha_' :: Term0 -> (([]) ((,) Prelude.String Prelude.String)) ->
                  (([]) Prelude.String) -> (Prelude.String -> Prelude.String
                  -> () -> () -> AlphaVar) -> (Prelude.String -> () -> () ->
                  AlphaVar) -> Alpha
to_GU__alpha_' s r used x x0 =
  term_rec (\s0 _ r0 x1 x2 _ ->
    let {o = lookup s0 r0} in
    case o of {
     Prelude.Just s1 -> Alpha_var s0 s1 r0 (x1 s0 s1 __ __);
     Prelude.Nothing -> Alpha_var s0 s0 r0 (x2 s0 __ __)})
    (\uSort s0 k s1 iHs used0 r0 x1 x2 _ ->
    let {p = to_GU_ used0 ((:) ((,) s0 (fresh_to_GU_ used0 r0 s0)) r0) s1} in
    case p of {
     (,) p0 t -> Alpha_lam uSort s0 (fresh_to_GU_ used0 r0 s0) k s1 t r0
      (let {iHs0 = iHs used0 ((:) ((,) s0 (fresh_to_GU_ used0 r0 s0)) r0)} in
       let {
        iHs1 = eq_rec_r
                 (to_GU_ used0 ((:) ((,) s0 (fresh_to_GU_ used0 r0 s0)) r0)
                   s1) iHs0 ((,) p0 t)}
       in
       iHs1 (\x3 y _ _ ->
         let {
          b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                s0 x3}
         in
         case b of {
          Prelude.True ->
           eq_rec_r x3 (\_ _ _ _ _ _ -> Alpha_var_cons x3
             (fresh_to_GU_ used0 r0 x3) r0) s0 iHs1 x1 x2 __ __ __;
          Prelude.False -> Alpha_var_diff s0 (fresh_to_GU_ used0 r0 s0) x3 y
           r0 (x1 x3 y __ __)}) (\x3 _ _ ->
         let {
          b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                s0 x3}
         in
         case b of {
          Prelude.True -> false_rec;
          Prelude.False -> Alpha_var_diff s0 (fresh_to_GU_ used0 r0 s0) x3 x3
           r0 (x2 x3 __ __)}) __)})
    (\bSort s1 iHs1 s2 iHs2 used0 r0 x1 x2 _ ->
    let {p1 = to_GU_ used0 r0 s1} in
    case p1 of {
     (,) p t ->
      case p of {
       (,) l l0 ->
        let {p2 = to_GU_ l r0 s2} in
        case p2 of {
         (,) p0 t0 -> Alpha_app bSort s1 t s2 t0 r0
          (let {iHs3 = iHs1 used0 r0} in
           eq_rec_r (to_GU_ used0 r0 s1) iHs3 ((,) ((,) l l0) t)
             (\x3 y _ _ -> x1 x3 y __ __) (\x3 _ _ -> x2 x3 __ __) __)
          (let {iHs3 = iHs2 l r0} in
           eq_rec_r (to_GU_ l r0 s2) iHs3 ((,) p0 t0) (\x3 y _ _ ->
             x1 x3 y __ __) (\x3 _ _ -> x2 x3 __ __) __)}}})
    (\d _ r0 _ _ _ -> Alpha_builtin r0 d) s used r x x0 __

to_GU__alpha_ :: Term0 -> (([]) ((,) Prelude.String Prelude.String)) -> (([])
                 Prelude.String) -> (Prelude.String -> Prelude.String -> ()
                 -> () -> AlphaVar) -> (Prelude.String -> () -> SigT
                 Prelude.String ()) -> Alpha
to_GU__alpha_ s r used =
  term_rec (\s0 _ r0 x _ ->
    let {o = lookup s0 r0} in
    case o of {
     Prelude.Just s1 -> Alpha_var s0 s1 r0 (x s0 s1 __ __);
     Prelude.Nothing -> Alpha_var s0 s0 r0 false_rec})
    (\uSort s0 k s1 iHs used0 r0 x x0 ->
    let {p = to_GU_ used0 ((:) ((,) s0 (fresh_to_GU_ used0 r0 s0)) r0) s1} in
    case p of {
     (,) p0 t -> Alpha_lam uSort s0 (fresh_to_GU_ used0 r0 s0) k s1 t r0
      (let {iHs0 = iHs used0 ((:) ((,) s0 (fresh_to_GU_ used0 r0 s0)) r0)} in
       let {
        iHs1 = eq_rec_r
                 (to_GU_ used0 ((:) ((,) s0 (fresh_to_GU_ used0 r0 s0)) r0)
                   s1) iHs0 ((,) p0 t)}
       in
       iHs1 (\x1 y _ _ ->
         let {
          b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                s0 x1}
         in
         case b of {
          Prelude.True ->
           eq_rec_r x1 (\_ _ _ _ _ -> Alpha_var_cons x1
             (fresh_to_GU_ used0 r0 x1) r0) s0 iHs1 x x0 __ __;
          Prelude.False -> Alpha_var_diff s0 (fresh_to_GU_ used0 r0 s0) x1 y
           r0 (x x1 y __ __)}) (\x1 _ ->
         let {
          b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                x1 s0}
         in
         case b of {
          Prelude.True ->
           eq_rec_r s0 (\_ -> ExistT (fresh_to_GU_ used0 r0 s0) __) x1 __;
          Prelude.False ->
           let {h0 = x0 x1} in
           let {h1 = h0 __} in case h1 of {
                                ExistT x2 _ -> ExistT x2 __}}))})
    (\bSort s1 iHs1 s2 iHs2 used0 r0 x x0 ->
    let {p1 = to_GU_ used0 r0 s1} in
    case p1 of {
     (,) p t ->
      case p of {
       (,) l l0 ->
        let {p2 = to_GU_ l r0 s2} in
        case p2 of {
         (,) p0 t0 -> Alpha_app bSort s1 t s2 t0 r0
          (let {iHs3 = iHs1 used0 r0} in
           eq_rec_r (to_GU_ used0 r0 s1) iHs3 ((,) ((,) l l0) t)
             (\x1 y _ _ -> x x1 y __ __) (\x1 _ -> x0 x1 __))
          (let {iHs3 = iHs2 l r0} in
           eq_rec_r (to_GU_ l r0 s2) iHs3 ((,) p0 t0) (\x1 y _ _ ->
             x x1 y __ __) (\x1 _ -> x0 x1 __))}}}) (\d _ r0 _ _ ->
    Alpha_builtin r0 d) s used r

map_creates_IdCtx :: (([]) Prelude.String) -> IdCtx
map_creates_IdCtx l =
  list_rec Id_ctx_nil (\a l0 iHl -> Id_ctx_cons a (map (\x -> (,) x x) l0)
    iHl) l

to_GU__alpha :: Term0 -> Alpha
to_GU__alpha s =
  let {s' = to_GU s} in
  let {r = map (\x -> (,) x x) (tv s)} in
  let {
   _evar_0_ = let {
               h = let {
                    h = let {_evar_0_ = map_creates_IdCtx (tv s)} in
                        eq_rec_r (map (\x -> (,) x x) (tv s)) _evar_0_ r}
                   in
                   to_GU__alpha_' s r (tv s) (\x y _ _ ->
                     lookup_some_IdCtx_then_alphavar r x y h) (\x _ _ ->
                     id_ctx_alphavar_refl r x h)}
              in
              alpha_weaken_ids r s (snd (to_GU_ (tv s) r s))
                (eq_rec_r (map (\x -> (,) x x) (tv s)) (\_ _ ->
                  let {l = tv s} in
                  list_rec Id_ctx_nil (\a l0 iHl -> Id_ctx_cons a
                    (map (\x -> (,) x x) l0) iHl) l) r __ h) h}
  in
  eq_rec_r (snd (to_GU_ (tv s) r s)) _evar_0_ s'

to_GU__GU_ :: Term0 -> (([]) ((,) Prelude.String Prelude.String)) -> (([])
              Prelude.String) -> GU
to_GU__GU_ s r used =
  term_rec (\s0 _ r0 _ _ ->
    let {o = lookup s0 r0} in
    case o of {
     Prelude.Just s1 -> GU_var s1;
     Prelude.Nothing -> GU_var s0}) (\uSort s0 k s1 iHs used0 r0 _ _ ->
    let {p = to_GU_ used0 ((:) ((,) s0 (fresh_to_GU_ used0 r0 s0)) r0) s1} in
    case p of {
     (,) p0 t -> GU_lam uSort (fresh_to_GU_ used0 r0 s0) k t
      (let {iHs0 = iHs used0 ((:) ((,) s0 (fresh_to_GU_ used0 r0 s0)) r0)} in
       eq_rec_r
         (to_GU_ used0 ((:) ((,) s0 (fresh_to_GU_ used0 r0 s0)) r0) s1) iHs0
         ((,) p0 t) __ __)}) (\bSort s1 iHs1 s2 iHs2 used0 r0 _ _ ->
    let {p1 = to_GU_ used0 r0 s1} in
    case p1 of {
     (,) p t ->
      case p of {
       (,) l l0 ->
        let {p2 = to_GU_ l r0 s2} in
        case p2 of {
         (,) p0 t0 -> GU_app bSort t t0
          (let {iHs3 = iHs1 used0 r0} in
           eq_rec_r (to_GU_ used0 r0 s1) iHs3 ((,) ((,) l l0) t) __ __)
          (let {iHs3 = iHs2 l r0} in
           eq_rec_r (to_GU_ l r0 s2) iHs3 ((,) p0 t0) __ __)}}})
    (\d _ _ _ _ -> GU_builtin d) s used r __ __

to_GU__GU :: Term0 -> GU
to_GU__GU s =
  to_GU__GU_ s (map (\x -> (,) x x) (tv s)) (tv s)

to_GU' :: Prelude.String -> Term0 -> Term0 -> Term0
to_GU' x t s =
  let {tvs = (:) x (app (tv t) (tv s))} in
  snd (to_GU_ tvs (map (\x0 -> (,) x0 x0) tvs) s)

to_GU'__alpha :: Prelude.String -> Term0 -> Term0 -> Alpha
to_GU'__alpha x t s =
  let {s' = to_GU' x t s} in
  let {r = map (\x0 -> (,) x0 x0) ((:) x (app (tv t) (tv s)))} in
  let {
   _evar_0_ = let {
               h = to_GU__alpha_' s r ((:) x (app (tv t) (tv s)))
                     (\x0 y _ _ ->
                     lookup_some_IdCtx_then_alphavar r x0 y
                       (let {
                         _evar_0_ = map_creates_IdCtx ((:) x
                                      (app (tv t) (tv s)))}
                        in
                        eq_rec_r
                          (map (\x1 -> (,) x1 x1) ((:) x
                            (app (tv t) (tv s)))) _evar_0_ r)) (\x0 _ _ ->
                     id_ctx_alphavar_refl r x0
                       (eq_rec_r
                         (map (\x1 -> (,) x1 x1) ((:) x (app (tv t) (tv s))))
                         (\_ _ ->
                         map_creates_IdCtx ((:) x (app (tv t) (tv s)))) r __
                         __))}
              in
              alpha_weaken_ids r s
                (snd (to_GU_ ((:) x (app (tv t) (tv s))) r s))
                (eq_rec_r
                  (map (\x0 -> (,) x0 x0) ((:) x (app (tv t) (tv s))))
                  (\_ _ ->
                  let {l = (:) x (app (tv t) (tv s))} in
                  list_rec Id_ctx_nil (\a l0 iHl -> Id_ctx_cons a
                    (map (\x0 -> (,) x0 x0) l0) iHl) l) r __ h) h}
  in
  eq_rec_r (snd (to_GU_ ((:) x (app (tv t) (tv s))) r s)) _evar_0_ s'

to_GU'__GU :: Prelude.String -> Term0 -> Term0 -> GU
to_GU'__GU x t s =
  to_GU__GU_ s (map (\x0 -> (,) x0 x0) ((:) x (app (tv t) (tv s)))) ((:) x
    (app (tv t) (tv s)))

to_GU'__NC :: Prelude.String -> Term0 -> Term0 -> NC
to_GU'__NC x t s =
  let {
   p = to_GU_ ((:) x (app (tv t) (tv s)))
         (map (\x0 -> (,) x0 x0) ((:) x (app (tv t) (tv s)))) s}
  in
  case p of {
   (,) _ t0 -> Nc_cons t0 x t ([]) (Nc_nil t0)}

to_GU_app_unfold :: BSort -> Term0 -> Term0 -> Term0 -> SigT Term0
                    (SigT Term0 ((,) ((,) () Alpha) Alpha))
to_GU_app_unfold b s t st =
  let {
   p = to_GU_ (app (tv s) (tv t)) (map (\x -> (,) x x) (app (tv s) (tv t))) s}
  in
  case p of {
   (,) p0 t0 ->
    let {q = to_GU_ (fst p0) (map (\x -> (,) x x) (app (tv s) (tv t))) t} in
    case q of {
     (,) _ t1 -> ExistT t0 (ExistT t1
      (let {
        h0 = eq_rec_r (Tmbin b t0 t1) (\_ ->
               let {
                _evar_0_ = alpha_sym (Tmbin b s t) (to_GU (Tmbin b s t)) ([])
                             ([]) Alpha_sym_nil (to_GU__alpha (Tmbin b s t))}
               in
               eq_rec_r (to_GU (Tmbin b s t)) _evar_0_ (Tmbin b t0 t1)) st __}
       in
       case h0 of {
        Alpha_var _ _ sigma x ->
         eq_rec_r ([]) (\_ -> false_rec) sigma __ __ x;
        Alpha_lam _ _ _ _ _ _ sigma x ->
         eq_rec_r ([]) (\_ -> false_rec) sigma __ __ x;
        Alpha_app b0 s1 s2 t2 t3 sigma x x0 ->
         eq_rec_r ([]) (\_ ->
           eq_rec_r b (\_ ->
             eq_rec_r t0 (\_ ->
               eq_rec_r t1 (\_ ->
                 eq_rec_r s (\_ ->
                   eq_rec_r t (\h4 h8 ->
                     eq_rec_r (Tmbin b t0 t1) (\_ -> (,) ((,) __
                       (alpha_extend_ids ([]) s t0 Id_ctx_nil
                         (alpha_extend_ids ([]) s t0 Id_ctx_nil
                           (alpha_extend_ids ([]) s t0 Id_ctx_nil
                             (alpha_sym t0 s (sym_alpha_ctx ([])) ([])
                               (sym_alpha_ctx_left_is_sym ([])) h4)))))
                       (alpha_extend_ids ([]) t t1 Id_ctx_nil
                         (alpha_extend_ids ([]) t t1 Id_ctx_nil
                           (alpha_extend_ids ([]) t t1 Id_ctx_nil
                             (alpha_sym t1 t (sym_alpha_ctx ([])) ([])
                               (sym_alpha_ctx_left_is_sym ([])) h8))))) st __)
                     t3) s2 __) t2) s1) b0 __ __) sigma __ __ x x0;
        Alpha_builtin r _ -> eq_rec_r ([]) (\_ -> false_rec) r __ __}))}}

to_GU_applam_unfold :: BSort -> USort -> Kind -> Term0 -> Term0 -> Term0 ->
                       Prelude.String -> SigT Prelude.String
                       (SigT Term0 (SigT Term0 ((,) ((,) () Alpha) Alpha)))
to_GU_applam_unfold bA bL a s t st x =
  let {h = to_GU_app_unfold bA (Tmabs bL x a s) t st} in
  case h of {
   ExistT x0 s0 ->
    case s0 of {
     ExistT x1 p ->
      case p of {
       (,) p0 a0 ->
        case p0 of {
         (,) _ a1 ->
          case a1 of {
           Alpha_var _ _ sigma x2 ->
            eq_rec_r ([]) (\_ -> false_rec) sigma __ __ x2;
           Alpha_lam b x2 y a2 s1 s2 sigma x3 ->
            eq_rec_r ([]) (\_ ->
              eq_rec_r bL (\_ ->
                eq_rec_r x (\_ ->
                  eq_rec_r a (\_ ->
                    eq_rec_r s (\_ h8 ->
                      eq_rec_r (Tmbin bA x0 x1) (\_ -> ExistT y (ExistT s2
                        (ExistT x1 ((,) ((,) __ h8) a0)))) st __) s1) a2) x2)
                b __ __ __) sigma __ __ x3;
           Alpha_app _ _ _ _ _ sigma x2 x3 ->
            eq_rec_r ([]) (\_ -> false_rec) sigma __ __ x2 x3;
           Alpha_builtin r _ -> eq_rec_r ([]) (\_ -> false_rec) r __ __}}}}}

to_GU'' :: Prelude.String -> Term0 -> Term0
to_GU'' x s =
  to_GU' x (Tmvar x) s

to_GU''__alpha :: Prelude.String -> Term0 -> Alpha
to_GU''__alpha x s =
  to_GU'__alpha x (Tmvar x) s

to_GU''__GU :: Prelude.String -> Term0 -> GU
to_GU''__GU x s =
  to_GU'__GU x (Tmvar x) s

to_GU''__GU_lam :: USort -> Prelude.String -> Kind -> Term0 -> GU
to_GU''__GU_lam b x a s =
  GU_lam b x a (to_GU'' x s) (to_GU'__GU x (Tmvar x) s)

sconstr2 :: Prelude.String -> Term0 -> Prelude.String -> Term0 -> Term0 ->
            (,) ((,) Term0 Term0) Term0
sconstr2 x0 t x p s =
  let {
   ftvs = app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))}
  in
  let {r = map (\x1 -> (,) x1 x1) ftvs} in
  (,) ((,) (snd (to_GU_ ftvs r s)) (snd (to_GU_ ftvs r t)))
  (snd (to_GU_ ftvs r p))

sconstr2_alpha_s :: Prelude.String -> Term0 -> Prelude.String -> Term0 ->
                    Term0 -> Term0 -> Term0 -> Term0 -> Alpha
sconstr2_alpha_s x0 t x p s s' t' p' =
  eq_rec_r
    (snd
      (to_GU_
        (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
        (map (\x1 -> (,) x1 x1)
          (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
        s)) (\_ ->
    eq_rec_r
      (snd
        (to_GU_
          (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
          (map (\x1 -> (,) x1 x1)
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) t))
      (\_ ->
      eq_rec_r
        (snd
          (to_GU_
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
            (map (\x1 -> (,) x1 x1)
              (app (ftv0 t)
                (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) p))
        (alpha_weaken_ids
          (map (\x1 -> (,) x1 x1)
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) s
          (snd
            (to_GU_
              (app (ftv0 t)
                (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
              (map (\x1 -> (,) x1 x1)
                (app (ftv0 t)
                  (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) s))
          (map_creates_IdCtx
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
          (to_GU__alpha_ s
            (map (\x1 -> (,) x1 x1)
              (app (ftv0 t)
                (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
            (\x1 y _ _ ->
            lookup_some_IdCtx_then_alphavar
              (map (\x2 -> (,) x2 x2)
                (app (ftv0 t)
                  (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) x1 y
              (map_creates_IdCtx
                (app (ftv0 t)
                  (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))))
            (\x1 _ -> ExistT x1 __))) p') t') s' __ __

sconstr2_alpha_t :: Prelude.String -> Term0 -> Prelude.String -> Term0 ->
                    Term0 -> Term0 -> Term0 -> Term0 -> Alpha
sconstr2_alpha_t x0 t x p s s' t' p' =
  eq_rec_r
    (snd
      (to_GU_
        (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
        (map (\x1 -> (,) x1 x1)
          (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
        s)) (\_ ->
    eq_rec_r
      (snd
        (to_GU_
          (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
          (map (\x1 -> (,) x1 x1)
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) t))
      (\_ ->
      eq_rec_r
        (snd
          (to_GU_
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
            (map (\x1 -> (,) x1 x1)
              (app (ftv0 t)
                (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) p))
        (alpha_weaken_ids
          (map (\x1 -> (,) x1 x1)
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) t
          (snd
            (to_GU_
              (app (ftv0 t)
                (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
              (map (\x1 -> (,) x1 x1)
                (app (ftv0 t)
                  (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) t))
          (map_creates_IdCtx
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
          (to_GU__alpha_ t
            (map (\x1 -> (,) x1 x1)
              (app (ftv0 t)
                (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
            (\x1 y _ _ ->
            lookup_some_IdCtx_then_alphavar
              (map (\x2 -> (,) x2 x2)
                (app (ftv0 t)
                  (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) x1 y
              (map_creates_IdCtx
                (app (ftv0 t)
                  (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))))
            (\x1 _ -> ExistT x1 __))) p') t') s' __ __

sconstr2_alpha_p :: Prelude.String -> Term0 -> Prelude.String -> Term0 ->
                    Term0 -> Term0 -> Term0 -> Term0 -> Alpha
sconstr2_alpha_p x0 t x p s s' t' p' =
  eq_rec_r
    (snd
      (to_GU_
        (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
        (map (\x1 -> (,) x1 x1)
          (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
        s)) (\_ ->
    eq_rec_r
      (snd
        (to_GU_
          (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
          (map (\x1 -> (,) x1 x1)
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) t))
      (\_ ->
      eq_rec_r
        (snd
          (to_GU_
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
            (map (\x1 -> (,) x1 x1)
              (app (ftv0 t)
                (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) p))
        (alpha_weaken_ids
          (map (\x1 -> (,) x1 x1)
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) p
          (snd
            (to_GU_
              (app (ftv0 t)
                (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
              (map (\x1 -> (,) x1 x1)
                (app (ftv0 t)
                  (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) p))
          (map_creates_IdCtx
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
          (to_GU__alpha_ p
            (map (\x1 -> (,) x1 x1)
              (app (ftv0 t)
                (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
            (\x1 y _ _ ->
            lookup_some_IdCtx_then_alphavar
              (map (\x2 -> (,) x2 x2)
                (app (ftv0 t)
                  (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) x1 y
              (map_creates_IdCtx
                (app (ftv0 t)
                  (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))))
            (\x1 _ -> ExistT x1 __))) p') t') s' __ __

sconstr2_nc_s :: Prelude.String -> Term0 -> Prelude.String -> Term0 -> Term0
                 -> Term0 -> Term0 -> Term0 -> NC
sconstr2_nc_s x0 t x p s s' t' p' =
  eq_rec_r
    (snd
      (to_GU_
        (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
        (map (\x1 -> (,) x1 x1)
          (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
        s)) (\_ ->
    eq_rec_r
      (snd
        (to_GU_
          (app (ftv0 t) (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
          (map (\x1 -> (,) x1 x1)
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) t))
      (\_ ->
      eq_rec_r
        (snd
          (to_GU_
            (app (ftv0 t)
              (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
            (map (\x1 -> (,) x1 x1)
              (app (ftv0 t)
                (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))) p))
        (let {
          gU_s = to_GU_
                   (app (ftv0 t)
                     (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
                   (map (\x1 -> (,) x1 x1)
                     (app (ftv0 t)
                       (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
                   s}
         in
         case gU_s of {
          (,) _ t0 ->
           let {
            gU_p = to_GU_
                     (app (ftv0 t)
                       (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([]))))))
                     (map (\x1 -> (,) x1 x1)
                       (app (ftv0 t)
                         (app (ftv0 p) (app (ftv0 s) ((:) x0 ((:) x ([])))))))
                     p}
           in
           case gU_p of {
            (,) _ t1 -> Nc_cons t0 x t1 ([]) (Nc_nil t0)}}) p') t') s' __ __

sconstr2_nc_s_t :: Prelude.String -> Term0 -> Prelude.String -> Term0 ->
                   Term0 -> Term0 -> Term0 -> Term0 -> NC
sconstr2_nc_s_t x0 _ _ _ _ s' t' _ =
  Nc_cons s' x0 t' ([]) (Nc_nil s')

sconstr2_nc_t :: Prelude.String -> Term0 -> Prelude.String -> Term0 -> Term0
                 -> Term0 -> Term0 -> Term0 -> NC
sconstr2_nc_t _ _ x _ _ _ t' p' =
  Nc_cons t' x p' ([]) (Nc_nil t')

sconstr2_nc_sub :: Prelude.String -> Term0 -> Prelude.String -> Term0 ->
                   Term0 -> Term0 -> Term0 -> Term0 -> NC
sconstr2_nc_sub x0 _ x _ _ s' t' p' =
  Nc_cons (psubs ((:) ((,) x p') ([])) s') x0
    (psubs ((:) ((,) x p') ([])) t') ([]) (Nc_nil
    (psubs ((:) ((,) x p') ([])) s'))

freshen2 :: (([]) Prelude.String) -> (([]) Prelude.String) -> ([])
            ((,) Prelude.String Prelude.String)
freshen2 used to_freshen =
  fold_right (\x acc ->
    let {fresh_var = fresh_to_GU_ (app used to_freshen) acc x} in
    (:) ((,) x fresh_var) acc) ([]) to_freshen

not_ftv_to_not_tv :: Prelude.String -> Term0 -> (,) () Alpha
not_ftv_to_not_tv x s =
  (,) __ (to_GU''__alpha x s)

alpha_extend_vacuous_ftv :: Prelude.String -> Prelude.String -> Term0 ->
                            Term0 -> (([])
                            ((,) Prelude.String Prelude.String)) -> Alpha ->
                            Alpha
alpha_extend_vacuous_ftv x x' s s' r x0 =
  let {h = not_ftv_to_not_tv x s} in
  case h of {
   (,) _ a ->
    let {h0 = not_ftv_to_not_tv x' s'} in
    case h0 of {
     (,) _ a0 ->
      let {
       h1 = alpha_trans3 r (to_GU'' x s) s s' (to_GU'' x' s')
              (alpha_sym s (to_GU'' x s) ([]) ([]) Alpha_sym_nil a) x0 a0}
      in
      alpha_trans3 ((:) ((,) x x') r) s (to_GU'' x s) (to_GU'' x' s') s' a
        (alpha_extend_vacuous x x' (to_GU'' x s) (to_GU'' x' s') r h1)
        (alpha_sym s' (to_GU'' x' s') ([]) ([]) Alpha_sym_nil a0)}}

alpha_vacuous_R :: Term0 -> Term0 -> (([])
                   ((,) Prelude.String Prelude.String)) -> (([])
                   ((,) Prelude.String Prelude.String)) -> Alpha -> Alpha
alpha_vacuous_R s s' r1 r2 x =
  list_rec (\_ _ -> eq_rec_r r2 x (app ([]) r2)) (\a r3 iHR1 _ _ ->
    case a of {
     (,) s0 s1 ->
      alpha_extend_vacuous_ftv s0 s1 s s'
        (let {
          app0 l m =
            case l of {
             ([]) -> m;
             (:) a0 l1 -> (:) a0 (app0 l1 m)}}
         in app0 r3 r2) (iHR1 __ __)}) r1 __ __

_UU03b1_ctx_vacuous_R :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
                         ((,) Prelude.String Term0)) -> (([])
                         ((,) Prelude.String Term0)) -> Coq__UU03b1_CtxSub ->
                         Coq__UU03b1_CtxSub
_UU03b1_ctx_vacuous_R r _UU03c3_ _UU03c3_' ha =
  list_rec (\_ _ _ ha0 ->
    case ha0 of {
     Alpha_ctx_nil r0 -> eq_rec_r ([]) (\_ _ -> Alpha_ctx_nil r) r0 __ __;
     Alpha_ctx_cons r0 _ _ _ _ _ _ x x0 x1 ->
      eq_rec_r ([]) (\_ -> false_rec) r0 __ __ x x0 x1})
    (\_ _UU03c3_0 iH_UU03c3_ _ _ _ ha0 ->
    case ha0 of {
     Alpha_ctx_nil r0 -> eq_rec_r ([]) (\_ -> false_rec) r0 __ __;
     Alpha_ctx_cons r0 _UU03c3_1 _UU03c3_'0 x y t t' x0 x1 x2 ->
      eq_rec_r ([]) (\_ ->
        eq_rec_r _UU03c3_0 (\_ h1 h3 h5 -> Alpha_ctx_cons r _UU03c3_0
          _UU03c3_'0 x y t t' (iH_UU03c3_ _UU03c3_'0 __ __ h1)
          (case h3 of {
            Alpha_var_refl x3 ->
             eq_rec_r x (\_ ->
               eq_rec_r y
                 (eq_rec_r y (\_ _ _ -> alphavar_refl_weaken_vacuouss y r) x
                   __ ha0 h3) x) x3 __;
            Alpha_var_cons _ _ _ -> false_rec __ __;
            Alpha_var_diff _ _ _ _ _ x3 -> false_rec __ __ __ __ x3})
          (let {h = alpha_vacuous_R t t' r ([]) h5} in
           let {_evar_0_ = \h0 -> h0} in eq_rec_r r _evar_0_ (app r ([])) h))
          _UU03c3_1) r0 __ __ x0 x1 x2}) _UU03c3_ _UU03c3_' __ __ ha

alpha_extend_fresh_tv :: Prelude.String -> Prelude.String -> (([])
                         ((,) Prelude.String Prelude.String)) -> Term0 ->
                         Term0 -> Alpha -> Alpha
alpha_extend_fresh_tv x x' ren t t' x0 =
  alpha_rec (\x1 y sigma a _ _ -> Alpha_var x1 y ((:) ((,) x x') sigma)
    (Alpha_var_diff x x' x1 y sigma a))
    (\b x1 y a s1 s2 sigma _ iHAlpha _ _ -> Alpha_lam b x1 y a s1 s2 ((:)
    ((,) x x') sigma)
    (alpha_swap s1 s2 ((:) ((,) x1 y) ((:) ((,) x x') sigma)) ((:) ((,) x x')
      ((:) ((,) x1 y) sigma)) (Lrs_start x x' x1 y sigma sigma
      (legalRenSwap_id sigma)) (iHAlpha __ __)))
    (\b s1 s2 t1 t2 sigma _ iHAlpha1 _ iHAlpha2 _ _ -> Alpha_app b s1 s2 t1
    t2 ((:) ((,) x x') sigma) (iHAlpha1 __ __) (iHAlpha2 __ __)) (\r d _ _ ->
    Alpha_builtin ((:) ((,) x x') r) d) ren t t' x0 __ __

alpha_extend_fresh :: Prelude.String -> Prelude.String -> (([])
                      ((,) Prelude.String Prelude.String)) -> Term0 -> Term0
                      -> Alpha -> Alpha
alpha_extend_fresh x x' ren t t' ha_t =
  let {tgu = to_GU'' x t} in
  let {t'gu = to_GU'' x' t'} in
  let {
   ht = alpha_trans tgu t t'gu (ctx_id_left ren) ren ren (id_left_trans ren)
          (alpha_extend_ids (ctx_id_left ren) tgu t (ctx_id_left_is_id ren)
            (eq_rec_r (to_GU'' x t)
              (alpha_sym t (to_GU'' x t) ([]) ([]) Alpha_sym_nil
                (to_GU''__alpha x t)) tgu))
          (alpha_trans t t' t'gu ren (ctx_id_right ren) ren
            (id_right_trans ren) ha_t
            (alpha_extend_ids (ctx_id_right ren) t' t'gu
              (ctx_id_right_is_id ren)
              (eq_rec_r (to_GU'' x' t') (to_GU''__alpha x' t') t'gu)))}
  in
  let {h1 = alpha_extend_fresh_tv x x' ren tgu t'gu ht} in
  alpha_trans t tgu t' (ctx_id_left ((:) ((,) x x') ren)) ((:) ((,) x x')
    ren) ((:) ((,) x x') ren) (id_left_trans ((:) ((,) x x') ren))
    (alpha_extend_ids (ctx_id_left ((:) ((,) x x') ren)) t tgu
      (ctx_id_left_is_id ((:) ((,) x x') ren))
      (eq_rec_r (to_GU'' x t) (\ht0 _ h2 ->
        eq_rec_r (to_GU'' x' t') (\_ _ _ -> to_GU''__alpha x t) t'gu ht0 __
          h2) tgu ht __ h1))
    (alpha_trans tgu t'gu t' ((:) ((,) x x') ren)
      (ctx_id_right ((:) ((,) x x') ren)) ((:) ((,) x x') ren)
      (id_right_trans ((:) ((,) x x') ren)) h1
      (alpha_extend_ids (ctx_id_right ((:) ((,) x x') ren)) t'gu t'
        (ctx_id_right_is_id ((:) ((,) x x') ren))
        (eq_rec_r (to_GU'' x t) (\ht0 _ h2 ->
          eq_rec_r (to_GU'' x' t') (\_ _ _ ->
            alpha_sym t' (to_GU'' x' t') ([]) ([]) Alpha_sym_nil
              (to_GU''__alpha x' t')) t'gu ht0 __ h2) tgu ht __ h1)))

alpha_ctx_ren_extend_fresh_ftv :: (([]) ((,) Prelude.String Term0)) -> (([])
                                  ((,) Prelude.String Term0)) ->
                                  Prelude.String -> Prelude.String -> (([])
                                  ((,) Prelude.String Prelude.String)) ->
                                  Coq__UU03b1_CtxSub -> Coq__UU03b1_CtxSub
alpha_ctx_ren_extend_fresh_ftv sigma sigma' x x' ren h__UU03b1_ =
  _UU03b1_CtxSub_rec (\r _ _ -> Alpha_ctx_nil ((:) ((,) x x') r))
    (\r _UU03c3_ _UU03c3_' x0 y t t' _ iHH__UU03b1_ a a0 _ _ ->
    Alpha_ctx_cons ((:) ((,) x x') r) _UU03c3_ _UU03c3_' x0 y t t'
    (iHH__UU03b1_ __ __) (Alpha_var_diff x x' x0 y r a)
    (alpha_extend_fresh x x' r t t' a0)) ren sigma sigma' h__UU03b1_ __ __

alpha_extend_id'' :: Term0 -> Prelude.String -> (([])
                     ((,) Prelude.String Prelude.String)) -> Alpha -> Alpha
alpha_extend_id'' s z ren =
  let {
   s0 = in_dec
          ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
          z (ftv0 s)}
  in
  (\x ->
  case s0 of {
   Prelude.True ->
    let {
     h0 = alpha_rec (\x0 y sigma a _ _ ->
            solution_left x0 (\sigma0 a0 _ ->
              eq_rec_r x0
                (list_rec (\_ -> Not_break_shadow_nil x0)
                  (\a1 sigma1 iHsigma a2 ->
                  case a1 of {
                   (,) s1 s2 ->
                    case a2 of {
                     Alpha_var_refl _ -> false_rec __ __;
                     Alpha_var_cons z0 w sigma2 ->
                      eq_rec_r s1 (\_ ->
                        eq_rec_r s2 (\_ ->
                          eq_rec_r sigma1 (\_ ->
                            eq_rec_r x0 (\_ ->
                              eq_rec_r x0
                                (eq_rec_r x0 (\a3 ->
                                  eq_rec_r x0 (\_ -> Not_break_shadow_id x0
                                    sigma1) s2 a3) s1 a2) s2) s1) sigma2) w)
                        z0 __ __ __ __;
                     Alpha_var_diff x1 y0 z0 w sigma2 x2 ->
                      eq_rec_r s1 (\_ ->
                        eq_rec_r s2 (\_ ->
                          eq_rec_r sigma1 (\_ ->
                            eq_rec_r x0 (\_ ->
                              eq_rec_r x0 (\_ _ h6 -> Not_break_shadow_cons
                                x0 s1 s2 sigma1 (iHsigma h6)) w) z0) sigma2)
                          y0) x1 __ __ __ __ __ __ x2}}) sigma0 a0) z) y
              sigma a __) (\_ x0 y a s1 s2 sigma h iHAlpha _ _ ->
            solution_left s1 (\sigma0 h0 iHAlpha0 _ _ ->
              solution_left x0 (\_ _ sigma1 _ iHAlpha1 _ ->
                let {iHAlpha2 = iHAlpha1 __ __} in
                case iHAlpha2 of {
                 Not_break_shadow_nil x1 ->
                  eq_rec_r z (\_ -> false_rec) x1 __;
                 Not_break_shadow_cons z0 x1 x' ren0 x2 ->
                  eq_rec_r z (\_ ->
                    eq_rec_r x0 (\_ ->
                      eq_rec_r x0 (\_ ->
                        eq_rec_r sigma1 (\_ _ h7 -> h7) ren0) x') x1 __ __)
                    z0 __ __ __ x2;
                 Not_break_shadow_id z0 ren0 ->
                  eq_rec_r z (\_ ->
                    eq_rec_r x0 (\_ ->
                      eq_rec_r x0 (\_ ->
                        eq_rec_r sigma1
                          (eq_rec_r x0 (\_ _ _ -> false_rec) z iHAlpha2 __
                            __) ren0) x0) z __ __) z0 __}) y a s1 sigma0 h0
                iHAlpha0 __) s2 sigma h iHAlpha __ __)
            (\_ s1 s2 t1 t2 sigma h iHAlpha1 h0 iHAlpha2 _ _ ->
            solution_left t1 (\sigma0 h1 h2 iHAlpha3 iHAlpha4 _ _ ->
              solution_left s1 (\t3 _ _ _ iHAlpha5 iHAlpha6 _ ->
                let {i = in_prop_to_set z (app (ftv0 s1) (ftv0 t3))} in
                let {i0 = in_app_or_set z (ftv0 s1) (ftv0 t3) i} in
                case i0 of {
                 Prelude.Left _ -> iHAlpha5 __ __;
                 Prelude.Right _ -> iHAlpha6 __ __}) s2 t1 sigma0 h1 h2
                iHAlpha3 iHAlpha4 __) t2 sigma h h0 iHAlpha1 iHAlpha2 __ __)
            (\_ _ _ _ -> Prelude.error "absurd case") ren s s x __ __}
    in
    alpha_extend_id' s s z ren x h0;
   Prelude.False -> alpha_extend_vacuous_ftv z z s s ren x})

a_R_constr :: (([]) ((,) Prelude.String Prelude.String)) -> Term0 -> Term0 ->
              Term0 -> ([]) ((,) Prelude.String Prelude.String)
a_R_constr r s s' t =
  let {
   used = app (tv s) (app (tv s') (app (tv t) (app (map fst r) (map snd r))))}
  in
  let {
   to_freshen = list_diff
                  ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                  (ftv0 t) (ftv0 s)}
  in
  let {rfr = freshen2 used to_freshen} in app rfr r

kindOfUniqueRhsFreshMultiple :: (([]) Prelude.String) -> (([])
                                ((,) Prelude.String Prelude.String)) -> (([])
                                Prelude.String) -> KindOfUniqueRhs ->
                                Prelude.String -> Prelude.String -> AlphaVar
kindOfUniqueRhsFreshMultiple used r l x x0 y =
  let {used' = app (app used (app (map fst r) (map snd r))) l} in
  let {h = ExistT l __} in
  case h of {
   ExistT x1 _ ->
    eq_rec_r (app (app used (app (map fst r) (map snd r))) x1)
      (list_rec (\h0 -> h0) (\a l0 iHl x2 ->
        let {
         _evar_0_ = let {
                     r'' = fold_right (\x3 acc -> (:) ((,) x3
                             (fresh_to_GU_
                               (app (app used (app (map fst r) (map snd r)))
                                 x1) acc x3)) acc) ([]) l0}
                    in
                    let {iHl0 = iHl x2} in
                    (\x3 x4 _ ->
                    kindOfUniqueRhsFresh a (app r'' r) r''
                      (app (app used (app (map fst r) (map snd r))) x1) iHl0
                      x3 x4)}
        in
        eq_rec_r
          (fold_right (\x3 acc -> (:) ((,) x3
            (fresh_to_GU_ (app (app used (app (map fst r) (map snd r))) x1)
              acc x3)) acc)
            (fold_right (\x3 acc -> (:) ((,) x3
              (fresh_to_GU_ (app (app used (app (map fst r) (map snd r))) x1)
                acc x3)) acc) ([]) l0) ((:) a ([]))) _evar_0_
          (fold_right (\x3 acc -> (:) ((,) x3
            (fresh_to_GU_ (app (app used (app (map fst r) (map snd r))) x1)
              acc x3)) acc) ([]) (app ((:) a ([])) l0))) l) used' x x0 y __}

a_R_constr_helper :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
                     ((,) Prelude.String Prelude.String)) -> Term0 -> Term0
                     -> Term0 -> Prelude.String -> Prelude.String -> Alpha ->
                     AlphaVar
a_R_constr_helper r r' s s' t x y _ =
  let {
   rfr = freshen2
           (app (tv s)
             (app (tv s') (app (tv t) (app (map fst r) (map snd r)))))
           (list_diff
             ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             (ftv0 t) (ftv0 s))}
  in
  let {
   _evar_0_ = \_ ->
    let {h1 = lookup_app_or_extended x y rfr r} in
    case h1 of {
     Prelude.Left _ ->
      let {_evar_0_ = lookup_some_then_alphavar (app rfr r) x y} in
      eq_rec_r (app rfr r) _evar_0_ r';
     Prelude.Right _ -> lookup_some_then_alphavar r' x y}}
  in
  eq_rec_r (app rfr r) _evar_0_ r' __

a_constr :: (([]) ((,) Prelude.String Prelude.String)) -> Term0 -> Term0 ->
            Term0 -> (,) (([]) ((,) Prelude.String Prelude.String)) Term0
a_constr r s s' t =
  let {r' = a_R_constr r s s' t} in
  let {
   used' = app (tv s)
             (app (tv s') (app (tv t) (app (map fst r') (map snd r'))))}
  in
  (,) r' (snd (to_GU_ used' r' t))

a_R_constr_alpha_s :: (([]) ((,) Prelude.String Prelude.String)) -> Term0 ->
                      Term0 -> Term0 -> (([])
                      ((,) Prelude.String Prelude.String)) -> Alpha -> Alpha
a_R_constr_alpha_s r s s' t r' x =
  let {
   rfr = freshen2
           (app (tv s)
             (app (tv s') (app (tv t) (app (map fst r) (map snd r)))))
           (list_diff
             ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             (ftv0 t) (ftv0 s))}
  in
  let {_evar_0_ = alpha_vacuous_R s s' rfr r x} in
  eq_rec_r (app rfr r) _evar_0_ r'

a_constr__t_alpha :: (([]) ((,) Prelude.String Prelude.String)) -> Term0 ->
                     Term0 -> Term0 -> (([])
                     ((,) Prelude.String Prelude.String)) -> Term0 -> Alpha
                     -> Alpha
a_constr__t_alpha r s s' t r' t' x =
  eq_rec_r (a_R_constr r s s' t) (\_ ->
    eq_rec_r
      (snd
        (to_GU_
          (app (tv s)
            (app (tv s')
              (app (tv t)
                (app (map fst (a_R_constr r s s' t))
                  (map snd (a_R_constr r s s' t)))))) (a_R_constr r s s' t)
          t))
      (to_GU__alpha_' t (a_R_constr r s s' t)
        (app (tv s)
          (app (tv s')
            (app (tv t)
              (app (map fst (a_R_constr r s s' t))
                (map snd (a_R_constr r s s' t)))))) (\x0 y _ _ ->
        a_R_constr_helper r (a_R_constr r s s' t) s s' t x0 y x) (\x0 _ _ ->
        alphavar_refl_weaken_vacuouss x0 r')) t') r' __

a_constr__s_alpha :: (([]) ((,) Prelude.String Prelude.String)) -> Term0 ->
                     Term0 -> Term0 -> (([])
                     ((,) Prelude.String Prelude.String)) -> Term0 -> Alpha
                     -> Alpha
a_constr__s_alpha r s s' t r' t' x =
  eq_rec_r (a_R_constr r s s' t) (\_ ->
    eq_rec_r
      (snd
        (to_GU_
          (app (tv s)
            (app (tv s')
              (app (tv t)
                (app (map fst (a_R_constr r s s' t))
                  (map snd (a_R_constr r s s' t)))))) (a_R_constr r s s' t)
          t))
      (let {h0 = a_R_constr_alpha_s r s s' t r' x} in
       eq_rec_r (a_R_constr r s s' t) (\_ h1 ->
         eq_rec_r
           (snd
             (to_GU_
               (app (tv s)
                 (app (tv s')
                   (app (tv t)
                     (app (map fst (a_R_constr r s s' t))
                       (map snd (a_R_constr r s s' t))))))
               (a_R_constr r s s' t) t)) (\_ -> h1) t' __) r' __ h0) t') r'
    __

r_constr :: Term0 -> Term0 -> (([]) ((,) Prelude.String Term0)) ->
            Prelude.String -> (,) (([]) ((,) Prelude.String Prelude.String))
            (([]) ((,) Prelude.String Prelude.String))
r_constr t s sigma x =
  let {tvs = app (tv s) (tv_keys_env sigma)} in
  let {btvs = app (btv s) (btv_env sigma)} in
  let {tv_t = tv t} in
  let {used = app tv_t (app tvs ((:) x ([])))} in
  let {
   r2 = map (\x0 -> (,) x0 x0)
          (list_diff
            ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
            (ftv0 t) btvs)}
  in
  let {r1 = freshen2 (app used (app (map fst r2) (map snd r2))) btvs} in
  (,) r1 r2

r_constr_R2_IdCtx :: Term0 -> Term0 -> (([]) ((,) Prelude.String Term0)) ->
                     Prelude.String -> (([])
                     ((,) Prelude.String Prelude.String)) -> (([])
                     ((,) Prelude.String Prelude.String)) -> IdCtx
r_constr_R2_IdCtx t s sigma x r1 r2 =
  eq_rec_r
    (freshen2
      (app (app (tv t) (app (app (tv s) (tv_keys_env sigma)) ((:) x ([]))))
        (app
          (map fst
            (map (\x0 -> (,) x0 x0)
              (list_diff
                ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                (ftv0 t) (app (btv s) (btv_env sigma)))))
          (map snd
            (map (\x0 -> (,) x0 x0)
              (list_diff
                ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                (ftv0 t) (app (btv s) (btv_env sigma)))))))
      (app (btv s) (btv_env sigma))) (\_ ->
    eq_rec_r
      (map (\x0 -> (,) x0 x0)
        (list_diff
          ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
          (ftv0 t) (app (btv s) (btv_env sigma))))
      (map_creates_IdCtx
        (list_diff
          ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
          (ftv0 t) (app (btv s) (btv_env sigma)))) r2) r1 __

t_constr :: Term0 -> Term0 -> (([]) ((,) Prelude.String Term0)) ->
            Prelude.String -> (,) Term0
            (([]) ((,) Prelude.String Prelude.String))
t_constr t s sigma x =
  let {tvs = app (tv s) (tv_keys_env sigma)} in
  let {tv_t = tv t} in
  let {used = app tv_t (app tvs ((:) x ([])))} in
  case r_constr t s sigma x of {
   (,) r1 r2 -> (,) (snd (to_GU_ used (app r1 r2) t)) (app r1 r2)}

t_constr__a_t :: Term0 -> Term0 -> (([]) ((,) Prelude.String Prelude.String))
                 -> Term0 -> (([]) ((,) Prelude.String Term0)) ->
                 Prelude.String -> Alpha
t_constr__a_t t t' r s sigma x =
  let {r' = r_constr t s sigma x} in
  case r' of {
   (,) l l0 ->
    eq_rec_r
      (snd
        (to_GU_
          (app (tv t) (app (app (tv s) (tv_keys_env sigma)) ((:) x ([]))))
          (app l l0) t)) (\_ ->
      eq_rec_r (app l l0)
        (to_GU__alpha_' t (app l l0)
          (app (tv t) (app (app (tv s) (tv_keys_env sigma)) ((:) x ([]))))
          (eq_rec_r
            (freshen2
              (app
                (app (tv t)
                  (app (app (tv s) (tv_keys_env sigma)) ((:) x ([]))))
                (app
                  (map fst
                    (map (\x0 -> (,) x0 x0)
                      (list_diff
                        ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                        (ftv0 t) (app (btv s) (btv_env sigma)))))
                  (map snd
                    (map (\x0 -> (,) x0 x0)
                      (list_diff
                        ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                        (ftv0 t) (app (btv s) (btv_env sigma)))))))
              (app (btv s) (btv_env sigma))) (\_ ->
            eq_rec_r
              (map (\x0 -> (,) x0 x0)
                (list_diff
                  ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                  (ftv0 t) (app (btv s) (btv_env sigma)))) (\x0 y _ _ ->
              kindOfUniqueRhsFreshMultiple
                (app (tv t)
                  (app (app (tv s) (tv_keys_env sigma)) ((:) x ([]))))
                (map (\x1 -> (,) x1 x1)
                  (list_diff
                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                    (ftv0 t) (app (btv s) (btv_env sigma))))
                (app (btv s) (btv_env sigma)) (\x1 x2 _ ->
                idCtx__KindOfUniqueRhs
                  (map (\x3 -> (,) x3 x3)
                    (list_diff
                      ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                      (ftv0 t) (app (btv s) (btv_env sigma))))
                  (map_creates_IdCtx
                    (list_diff
                      ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                      (ftv0 t) (app (btv s) (btv_env sigma)))) x1 x2) x0 y)
              l0) l __) (\_ _ _ -> false_rec)) r) t' __}

r_constr__a_s :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
                 ((,) Prelude.String Prelude.String)) -> Term0 -> Term0 ->
                 (([]) ((,) Prelude.String Term0)) -> Prelude.String -> GU ->
                 Alpha
r_constr__a_s r1 r2 t s sigma x _ =
  alpha_vacuous_R s s r1 r2
    (alpha_extend_ids r2 s s
      (eq_rec_r
        (freshen2
          (app
            (app (tv t) (app (app (tv s) (tv_keys_env sigma)) ((:) x ([]))))
            (app
              (map fst
                (map (\x0 -> (,) x0 x0)
                  (list_diff
                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                    (ftv0 t) (app (btv s) (btv_env sigma)))))
              (map snd
                (map (\x0 -> (,) x0 x0)
                  (list_diff
                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                    (ftv0 t) (app (btv s) (btv_env sigma)))))))
          (app (btv s) (btv_env sigma))) (\_ ->
        eq_rec_r
          (map (\x0 -> (,) x0 x0)
            (list_diff
              ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
              (ftv0 t) (app (btv s) (btv_env sigma))))
          (map_creates_IdCtx
            (list_diff
              ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
              (ftv0 t) (app (btv s) (btv_env sigma)))) r2) r1 __)
      (alpha_refl s ([]) Alpha_refl_nil))

t_constr__a_s :: Term0 -> Term0 -> (([]) ((,) Prelude.String Prelude.String))
                 -> Term0 -> (([]) ((,) Prelude.String Term0)) ->
                 Prelude.String -> GU -> Alpha
t_constr__a_s t t' r s sigma x x0 =
  let {p = r_constr t s sigma x} in
  case p of {
   (,) l l0 ->
    eq_rec_r
      (snd
        (to_GU_
          (app (tv t) (app (app (tv s) (tv_keys_env sigma)) ((:) x ([]))))
          (app l l0) t)) (\_ ->
      eq_rec_r (app l l0) (r_constr__a_s l l0 t s sigma x x0) r) t' __}

r_constr__a_sigma :: (([]) ((,) Prelude.String Prelude.String)) -> (([])
                     ((,) Prelude.String Prelude.String)) -> Term0 -> Term0
                     -> (([]) ((,) Prelude.String Term0)) -> Prelude.String
                     -> NC -> Coq__UU03b1_CtxSub
r_constr__a_sigma r1 r2 t s sigma x _ =
  _UU03b1_ctx_sub_extend_ids_right sigma sigma r1 r2
    (r_constr_R2_IdCtx t s sigma x r1 r2)
    (_UU03b1_ctx_vacuous_R r1 sigma sigma (alpha_ctx_ren_nil sigma))

t_constr__a_sigma :: Term0 -> Term0 -> (([])
                     ((,) Prelude.String Prelude.String)) -> Term0 -> (([])
                     ((,) Prelude.String Term0)) -> Prelude.String -> NC ->
                     Coq__UU03b1_CtxSub
t_constr__a_sigma t t' r s sigma x x0 =
  let {p = r_constr t s sigma x} in
  case p of {
   (,) l l0 ->
    eq_rec_r
      (snd
        (to_GU_
          (app (tv t) (app (app (tv s) (tv_keys_env sigma)) ((:) x ([]))))
          (app l l0) t)) (\_ ->
      eq_rec_r (app l l0) (r_constr__a_sigma l l0 t s sigma x x0) r) t' __}

t_constr__nc_s :: Term0 -> Term0 -> (([])
                  ((,) Prelude.String Prelude.String)) -> Term0 -> (([])
                  ((,) Prelude.String Term0)) -> Prelude.String -> NC -> NC
t_constr__nc_s _ t' _ s sigma x x0 =
  Nc_cons s x t' sigma x0

t_constr__nc_subs :: Term0 -> Term0 -> (([])
                     ((,) Prelude.String Prelude.String)) -> Term0 -> (([])
                     ((,) Prelude.String Term0)) -> Prelude.String -> NC
t_constr__nc_subs _ t' _ s sigma x =
  Nc_cons (psubs sigma s) x t' ([]) (Nc_nil (psubs sigma s))

s_constr :: Term0 -> (([]) ((,) Prelude.String Term0)) -> Term0
s_constr s sigma =
  let {tvs = app (tv_keys_env sigma) (tv s)} in
  snd (to_GU_ tvs (map (\x -> (,) x x) tvs) s)

s_constr__a_s :: Term0 -> Term0 -> (([]) ((,) Prelude.String Term0)) -> Alpha
s_constr__a_s s s' sigma =
  let {r = map (\x -> (,) x x) (app (tv_keys_env sigma) (tv s))} in
  let {
   _evar_0_ = let {
               h = let {
                    _evar_0_ = to_GU__alpha_' s r
                                 (app (tv_keys_env sigma) (tv s))
                                 (\x y _ _ ->
                                 lookup_some_IdCtx_then_alphavar r x y
                                   (let {
                                     _evar_0_ = map_creates_IdCtx
                                                  (app (tv_keys_env sigma)
                                                    (tv s))}
                                    in
                                    eq_rec_r
                                      (map (\x0 -> (,) x0 x0)
                                        (app (tv_keys_env sigma) (tv s)))
                                      _evar_0_ r)) (\x _ _ ->
                                 id_ctx_alphavar_refl r x
                                   (eq_rec_r
                                     (map (\x0 -> (,) x0 x0)
                                       (app (tv_keys_env sigma) (tv s)))
                                     (\_ _ ->
                                     map_creates_IdCtx
                                       (app (tv_keys_env sigma) (tv s))) r __
                                     __))}
                   in
                   eq_rec_r
                     (snd (to_GU_ (app (tv_keys_env sigma) (tv s)) r s))
                     _evar_0_ s'}
              in
              alpha_weaken_ids r s
                (snd (to_GU_ (app (tv_keys_env sigma) (tv s)) r s))
                (eq_rec_r
                  (map (\x -> (,) x x) (app (tv_keys_env sigma) (tv s)))
                  (\_ h0 ->
                  eq_rec_r
                    (snd
                      (to_GU_ (app (tv_keys_env sigma) (tv s))
                        (map (\x -> (,) x x)
                          (app (tv_keys_env sigma) (tv s))) s)) (\_ ->
                    let {l = app (tv_keys_env sigma) (tv s)} in
                    list_rec Id_ctx_nil (\a l0 iHl -> Id_ctx_cons a
                      (map (\x -> (,) x x) l0) iHl) l) s' h0) r __ h)
                (eq_rec_r
                  (map (\x -> (,) x x) (app (tv_keys_env sigma) (tv s)))
                  (\_ h0 ->
                  eq_rec_r
                    (snd
                      (to_GU_ (app (tv_keys_env sigma) (tv s))
                        (map (\x -> (,) x x)
                          (app (tv_keys_env sigma) (tv s))) s)) (\h1 -> h1)
                    s' h0) r __ h)}
  in
  eq_rec_r (snd (to_GU_ (app (tv_keys_env sigma) (tv s)) r s)) _evar_0_ s'

s_constr__gu :: Term0 -> Term0 -> (([]) ((,) Prelude.String Term0)) -> GU
s_constr__gu s s' sigma =
  eq_rec_r
    (snd
      (to_GU_ (app (tv_keys_env sigma) (tv s))
        (map (\x -> (,) x x) (app (tv_keys_env sigma) (tv s))) s))
    (to_GU__GU_ s (map (\x -> (,) x x) (app (tv_keys_env sigma) (tv s)))
      (app (tv_keys_env sigma) (tv s))) s'

s_constr__nc_s :: Term0 -> Term0 -> (([]) ((,) Prelude.String Term0)) -> NC
s_constr__nc_s s s' sigma =
  eq_rec_r (s_constr s sigma)
    (let {
      p = to_GU_ (app (tv_keys_env sigma) (tv s))
            (map (\x -> (,) x x) (app (tv_keys_env sigma) (tv s))) s}
     in
     nc_helper (snd p) sigma) s'

alpha_rename_binder_stronger :: Prelude.String -> Prelude.String -> Term0 ->
                                Term0 -> Term0 -> (([])
                                ((,) Prelude.String Prelude.String)) -> Term0
                                -> (([]) ((,) Prelude.String Prelude.String))
                                -> Alpha -> Alpha -> LegalRenSwaps -> NC ->
                                NC -> Alpha
alpha_rename_binder_stronger x y s t t' rt s' rs x0 x1 x2 x3 x4 =
  term_rec (\s0 _ _ h3 _ h2 rs0 h rt0 h0 h1 ->
    case h of {
     Alpha_var x5 y0 sigma x6 ->
      eq_rec_r rs0 (\_ ->
        eq_rec_r s0 (\_ _ ->
          let {
           b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 x s0}
          in
          case b of {
           Prelude.True ->
            eq_rec_r s0 (\_ h4 ->
              let {
               b0 = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                      y y0}
              in
              case b0 of {
               Prelude.True -> eq_rec_r y0 (\_ _ -> h0) y h3 h4;
               Prelude.False -> false_rec}) x h2 h1;
           Prelude.False ->
            let {
             b0 = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                    y y0}
            in
            case b0 of {
             Prelude.True -> eq_rec_r y0 (\_ _ -> false_rec) y h3 h1;
             Prelude.False ->
              let {
               h4 = alpha_swaps (Tmvar s0) (Tmvar y0) ((:) ((,) x y) rt0) rs0
                      (lrss_sym ((:) ((,) x y) rt0) rs0 h1) h}
              in
              case h4 of {
               Alpha_var x7 y1 sigma0 x8 ->
                eq_rec_r ((:) ((,) x y) rt0) (\_ ->
                  eq_rec_r s0 (\_ ->
                    eq_rec_r y0 (\h10 ->
                      case h10 of {
                       Alpha_var_refl _ -> false_rec __ __;
                       Alpha_var_cons z w sigma1 ->
                        eq_rec_r x (\_ ->
                          eq_rec_r y (\_ ->
                            eq_rec_r rt0 (\_ ->
                              eq_rec_r s0 (\_ ->
                                eq_rec_r y0
                                  (eq_rec_r s0 (\_ h5 h6 _ h11 ->
                                    eq_rec_r y0 (\_ _ _ _ _ -> false_rec) y
                                      h3 h5 h6 __ h11) x h2 h4 h1 __ h10) y)
                                x) sigma1) w) z __ __ __ __;
                       Alpha_var_diff x9 y2 z w sigma1 x10 ->
                        eq_rec_r x (\_ ->
                          eq_rec_r y (\_ ->
                            eq_rec_r rt0 (\_ ->
                              eq_rec_r s0 (\_ ->
                                eq_rec_r y0 (\_ _ h15 -> Alpha_var s0 y0 rt0
                                  h15) w) z) sigma1) y2) x9 __ __ __ __ __ __
                          x10}) y1) x7) sigma0 __ __ x8;
               Alpha_lam _ _ _ _ _ _ sigma0 x7 ->
                eq_rec_r ((:) ((,) x y) rt0) (\_ -> false_rec) sigma0 __ __
                  x7;
               Alpha_app _ _ _ _ _ sigma0 x7 x8 ->
                eq_rec_r ((:) ((,) x y) rt0) (\_ -> false_rec) sigma0 __ __
                  x7 x8;
               Alpha_builtin r _ ->
                eq_rec_r ((:) ((,) x y) rt0) (\_ -> false_rec) r __ __}}}) x5)
        sigma __ __ x6;
     Alpha_lam _ _ _ _ _ _ sigma x5 ->
      eq_rec_r rs0 (\_ -> false_rec) sigma __ __ x5;
     Alpha_app _ _ _ _ _ sigma x5 x6 ->
      eq_rec_r rs0 (\_ -> false_rec) sigma __ __ x5 x6;
     Alpha_builtin r _ -> eq_rec_r rs0 (\_ -> false_rec) r __ __})
    (\uSort s0 k s1 iHs _ t'0 h3 t0 h2 rs0 h rt0 h0 h1 ->
    case h of {
     Alpha_var _ _ sigma x5 -> eq_rec_r rs0 (\_ -> false_rec) sigma __ __ x5;
     Alpha_lam b x5 y0 a s2 s3 sigma x6 ->
      eq_rec_r rs0 (\_ ->
        eq_rec_r uSort (\_ ->
          eq_rec_r s0 (\_ ->
            eq_rec_r k (\_ ->
              eq_rec_r s1 (\_ h10 -> Alpha_lam uSort s0 y0 k (sub x t0 s1)
                (sub y t'0 s3) rt0
                (iHs s3 t'0 (nc_lam uSort y0 s3 k ((:) ((,) y t'0) ([])) h3)
                  t0 (nc_lam uSort s0 s1 k ((:) ((,) x t0) ([])) h2) ((:)
                  ((,) s0 y0) rs0) h10 ((:) ((,) s0 y0) rt0)
                  (alpha_extend_vacuous_ftv s0 y0 t0 t'0 rt0 h0)
                  (lrss_trans ((:) ((,) x y) ((:) ((,) s0 y0) rt0)) ((:) ((,)
                    s0 y0) ((:) ((,) x y) rt0)) ((:) ((,) s0 y0) rs0) (StarSE
                    ((:) ((,) x y) ((:) ((,) s0 y0) rt0)) ((:) ((,) s0 y0)
                    ((:) ((,) x y) rt0)) StarR (Lrs_start x y s0 y0 rt0 rt0
                    (legalRenSwap_id rt0)))
                    (lrss_cons s0 y0 ((:) ((,) x y) rt0) rs0 h1)))) s2) a) x5)
          b __ __ __) sigma __ __ x6;
     Alpha_app _ _ _ _ _ sigma x5 x6 ->
      eq_rec_r rs0 (\_ -> false_rec) sigma __ __ x5 x6;
     Alpha_builtin r _ -> eq_rec_r rs0 (\_ -> false_rec) r __ __})
    (\bSort s1 iHs1 s2 iHs2 _ t'0 h3 t0 h2 rs0 h rt0 h0 h1 ->
    case h of {
     Alpha_var _ _ sigma x5 -> eq_rec_r rs0 (\_ -> false_rec) sigma __ __ x5;
     Alpha_lam _ _ _ _ _ _ sigma x5 ->
      eq_rec_r rs0 (\_ -> false_rec) sigma __ __ x5;
     Alpha_app b s3 s4 t1 t2 sigma x5 x6 ->
      eq_rec_r rs0 (\_ ->
        eq_rec_r bSort (\_ ->
          eq_rec_r s1 (\_ ->
            eq_rec_r s2 (\_ h9 h10 -> Alpha_app bSort (sub x t0 s1)
              (sub y t'0 s4) (sub x t0 s2) (sub y t'0 t2) rt0
              (iHs1 s4 t'0 (nc_app_l bSort s4 t2 ((:) ((,) y t'0) ([])) h3)
                t0 (nc_app_l bSort s1 s2 ((:) ((,) x t0) ([])) h2) rs0 h9 rt0
                h0 h1)
              (iHs2 t2 t'0 (nc_app_r bSort s4 t2 ((:) ((,) y t'0) ([])) h3)
                t0 (nc_app_r bSort s1 s2 ((:) ((,) x t0) ([])) h2) rs0 h10
                rt0 h0 h1)) t1) s3) b __ __) sigma __ __ x5 x6;
     Alpha_builtin r _ -> eq_rec_r rs0 (\_ -> false_rec) r __ __})
    (\d _ _ _ _ _ rs0 h rt0 _ _ ->
    case h of {
     Alpha_var _ _ sigma x5 -> eq_rec_r rs0 (\_ -> false_rec) sigma __ __ x5;
     Alpha_lam _ _ _ _ _ _ sigma x5 ->
      eq_rec_r rs0 (\_ -> false_rec) sigma __ __ x5;
     Alpha_app _ _ _ _ _ sigma x5 x6 ->
      eq_rec_r rs0 (\_ -> false_rec) sigma __ __ x5 x6;
     Alpha_builtin r d0 ->
      eq_rec_r rs0 (\_ -> eq_rec_r d (\_ -> Alpha_builtin rt0 d) d0) r __ __})
    s s' t' x4 t x3 rs x0 rt x1 x2

psubs___UU03b1_ :: Term0 -> (([]) ((,) Prelude.String Prelude.String)) ->
                   Term0 -> (([]) ((,) Prelude.String Term0)) -> (([])
                   ((,) Prelude.String Term0)) -> NC -> NC -> Alpha ->
                   Coq__UU03b1_CtxSub -> Alpha
psubs___UU03b1_ s =
  term_rec (\s0 r _ sigma sigma' _ _ x x0 ->
    case x of {
     Alpha_var x1 y sigma0 x2 ->
      eq_rec_r r (\_ ->
        eq_rec_r s0 (\_ h5 ->
          let {o = lookup s0 sigma} in
          case o of {
           Prelude.Just t ->
            let {s1 = alpha_ctx_right_ex r sigma sigma' s0 y t x0 h5} in
            case s1 of {
             ExistT x3 p ->
              case p of {
               (,) _ a -> eq_rec_r (Prelude.Just x3) a (lookup y sigma')}};
           Prelude.Nothing ->
            let {_evar_0_ = Alpha_var s0 y r h5} in
            eq_rec_r Prelude.Nothing _evar_0_ (lookup y sigma')}) x1) sigma0
        __ __ x2;
     Alpha_lam _ _ _ _ _ _ sigma0 x1 ->
      eq_rec_r r (\_ -> false_rec) sigma0 __ __ x1;
     Alpha_app _ _ _ _ _ sigma0 x1 x2 ->
      eq_rec_r r (\_ -> false_rec) sigma0 __ __ x1 x2;
     Alpha_builtin r0 _ -> eq_rec_r r (\_ -> false_rec) r0 __ __})
    (\uSort s0 k s1 iHs r _ sigma sigma' x x0 x1 x2 ->
    case x1 of {
     Alpha_var _ _ sigma0 x3 -> eq_rec_r r (\_ -> false_rec) sigma0 __ __ x3;
     Alpha_lam b x3 y a s2 s3 sigma0 x4 ->
      eq_rec_r r (\_ ->
        eq_rec_r uSort (\_ ->
          eq_rec_r s0 (\_ ->
            eq_rec_r k (\_ ->
              eq_rec_r s1 (\_ h9 -> Alpha_lam uSort s0 y k (psubs sigma s1)
                (psubs sigma' s3) r
                (iHs ((:) ((,) s0 y) r) s3 sigma sigma'
                  (nc_lam uSort s0 s1 k sigma x)
                  (nc_lam uSort y s3 k sigma' x0) h9
                  (alpha_ctx_ren_extend_fresh_ftv sigma sigma' s0 y r x2)))
                s2) a) x3) b __ __ __) sigma0 __ __ x4;
     Alpha_app _ _ _ _ _ sigma0 x3 x4 ->
      eq_rec_r r (\_ -> false_rec) sigma0 __ __ x3 x4;
     Alpha_builtin r0 _ -> eq_rec_r r (\_ -> false_rec) r0 __ __})
    (\bSort s1 iHs1 s2 iHs2 r _ sigma sigma' x x0 x1 x2 ->
    case x1 of {
     Alpha_var _ _ sigma0 x3 -> eq_rec_r r (\_ -> false_rec) sigma0 __ __ x3;
     Alpha_lam _ _ _ _ _ _ sigma0 x3 ->
      eq_rec_r r (\_ -> false_rec) sigma0 __ __ x3;
     Alpha_app b s3 s4 t1 t2 sigma0 x3 x4 ->
      eq_rec_r r (\_ ->
        eq_rec_r bSort (\_ ->
          eq_rec_r s1 (\_ ->
            eq_rec_r s2 (\_ h8 h9 -> Alpha_app bSort (psubs sigma s1)
              (psubs sigma' s4) (psubs sigma s2) (psubs sigma' t2) r
              (iHs1 r s4 sigma sigma' (nc_app_l bSort s1 s2 sigma x)
                (nc_app_l bSort s4 t2 sigma' x0) h8 x2)
              (iHs2 r t2 sigma sigma' (nc_app_r bSort s1 s2 sigma x)
                (nc_app_r bSort s4 t2 sigma' x0) h9 x2)) t1) s3) b __ __)
        sigma0 __ __ x3 x4;
     Alpha_builtin r0 _ -> eq_rec_r r (\_ -> false_rec) r0 __ __})
    (\d r _ _ _ _ _ x _ ->
    case x of {
     Alpha_var _ _ sigma x0 -> eq_rec_r r (\_ -> false_rec) sigma __ __ x0;
     Alpha_lam _ _ _ _ _ _ sigma x0 ->
      eq_rec_r r (\_ -> false_rec) sigma __ __ x0;
     Alpha_app _ _ _ _ _ sigma x0 x1 ->
      eq_rec_r r (\_ -> false_rec) sigma __ __ x0 x1;
     Alpha_builtin r0 d0 ->
      eq_rec_r r (\_ -> eq_rec_r d (\_ -> Alpha_builtin r d) d0) r0 __ __}) s

commute_sub_naive :: (([]) ((,) Prelude.String Prelude.String)) ->
                     Prelude.String -> Term0 -> Term0 -> (([])
                     ((,) Prelude.String Term0)) -> (([])
                     ((,) Prelude.String Term0)) -> Term0 -> Alpha ->
                     Coq__UU03b1_CtxSub -> NC -> NC -> NC -> NC -> NC ->
                     Alpha
commute_sub_naive r x s t sigma sigma' xtsAlpha ha_sub hctx__UU03c3_ hNC_sub hNC_s_x hNC_s__UU03c3_ hNC_t__UU03c3_ hNC_subs =
  term_rec
    (\s0 hNC_s_x0 hNC_s__UU03c3_0 hNC_subs0 r0 hctx__UU03c3_0 xtsAlpha0 ha_sub0 hNC_sub0 ->
    let {
     b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
           s0}
    in
    case b of {
     Prelude.True ->
      eq_rec_r s0 (\_ _ _ _ ha_sub1 ->
        let {
         _evar_0_ = \ha_sub2 ->
          let {
           s1 = in_dec
                  ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                  s0 (map fst sigma)}
          in
          case s1 of {
           Prelude.True -> false_rec;
           Prelude.False ->
            let {
             _evar_0_ = let {
                         _evar_0_ = psubs___UU03b1_ t r0 xtsAlpha0 sigma
                                      sigma' hNC_t__UU03c3_ hNC_sub0 ha_sub2
                                      hctx__UU03c3_0}
                        in
                        eq_rec_r Prelude.True _evar_0_
                          (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                            s0 s0)}
            in
            eq_rec_r (Tmvar s0) _evar_0_ (psubs sigma (Tmvar s0))}}
        in
        eq_rec_r Prelude.True _evar_0_
          (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
            s0 s0) ha_sub1) x __ __ hNC_s_x0 hNC_subs0 ha_sub0;
     Prelude.False ->
      let {
       _evar_0_ = \ha_sub1 ->
        case ha_sub1 of {
         Alpha_var x0 y sigma0 x1 ->
          eq_rec_r r0 (\_ ->
            eq_rec_r s0 (\_ _ ->
              let {
               s1 = in_dec
                      ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                      s0 (map fst sigma)}
              in
              case s1 of {
               Prelude.True ->
                let {
                 _evar_0_ = psubs___UU03b1_ (Tmvar s0) r0 (Tmvar y) sigma
                              sigma' hNC_s__UU03c3_0 hNC_sub0 ha_sub1
                              hctx__UU03c3_0}
                in
                eq_rec_r (psubs sigma (Tmvar s0)) _evar_0_
                  (sub x (psubs sigma t) (psubs sigma (Tmvar s0)));
               Prelude.False ->
                let {
                 _evar_0_ = let {
                             _evar_0_ = psubs___UU03b1_ (Tmvar s0) r0 (Tmvar
                                          y) sigma sigma' hNC_s__UU03c3_0
                                          hNC_sub0 ha_sub1 hctx__UU03c3_0}
                            in
                            eq_rec_r Prelude.False _evar_0_
                              (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                x s0)}
                in
                eq_rec_r (Tmvar s0) _evar_0_ (psubs sigma (Tmvar s0))}) x0)
            sigma0 __ __ x1;
         Alpha_lam _ _ _ _ _ _ sigma0 x0 ->
          eq_rec_r r0 (\_ -> false_rec) sigma0 __ __ x0;
         Alpha_app _ _ _ _ _ sigma0 x0 x1 ->
          eq_rec_r r0 (\_ -> false_rec) sigma0 __ __ x0 x1;
         Alpha_builtin r1 _ -> eq_rec_r r0 (\_ -> false_rec) r1 __ __}}
      in
      eq_rec_r Prelude.False _evar_0_
        (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
          s0) ha_sub0})
    (\uSort s0 k s1 iHs hNC_s_x0 hNC_s__UU03c3_0 hNC_subs0 r0 hctx__UU03c3_0 _ ha_sub0 hNC_sub0 ->
    case ha_sub0 of {
     Alpha_var _ _ sigma0 x0 -> eq_rec_r r0 (\_ -> false_rec) sigma0 __ __ x0;
     Alpha_lam b x0 y a s2 s3 sigma0 x1 ->
      eq_rec_r r0 (\_ ->
        eq_rec_r uSort (\_ ->
          eq_rec_r s0 (\_ ->
            eq_rec_r k (\_ ->
              eq_rec_r (sub x t s1) (\_ h5 -> Alpha_lam uSort s0 y k
                (let {
                  sub0 x2 u t0 =
                    case t0 of {
                     Tmvar y0 ->
                      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                             x2 y0 of {
                       Prelude.True -> u;
                       Prelude.False -> Tmvar y0};
                     Tmabs b0 y0 k1 t' -> Tmabs b0 y0 k1 (sub0 x2 u t');
                     Tmbin b0 t1 t2 -> Tmbin b0 (sub0 x2 u t1) (sub0 x2 u t2);
                     Tmbuiltin d -> Tmbuiltin d}}
                 in sub0 x (psubs sigma t)
                      (let {
                        psubs0 sigma1 t0 =
                          case t0 of {
                           Tmvar x2 ->
                            case lookup x2 sigma1 of {
                             Prelude.Just t1 -> t1;
                             Prelude.Nothing -> Tmvar x2};
                           Tmabs b0 x2 a0 s4 -> Tmabs b0 x2 a0
                            (psubs0 sigma1 s4);
                           Tmbin b0 s4 t1 -> Tmbin b0 (psubs0 sigma1 s4)
                            (psubs0 sigma1 t1);
                           Tmbuiltin d -> Tmbuiltin d}}
                       in psubs0 sigma s1))
                (let {
                  psubs0 sigma1 t0 =
                    case t0 of {
                     Tmvar x2 ->
                      case lookup x2 sigma1 of {
                       Prelude.Just t1 -> t1;
                       Prelude.Nothing -> Tmvar x2};
                     Tmabs b0 x2 a0 s4 -> Tmabs b0 x2 a0 (psubs0 sigma1 s4);
                     Tmbin b0 s4 t1 -> Tmbin b0 (psubs0 sigma1 s4)
                      (psubs0 sigma1 t1);
                     Tmbuiltin d -> Tmbuiltin d}}
                 in psubs0 sigma' s3) r0
                (iHs (nc_lam uSort s0 s1 k ((:) ((,) x t) ([])) hNC_s_x0)
                  (nc_lam uSort s0 s1 k sigma hNC_s__UU03c3_0)
                  (nc_lam uSort s0 (psubs sigma s1) k ((:) ((,) x
                    (psubs sigma t)) ([])) hNC_subs0) ((:) ((,) s0 y) r0)
                  (alpha_ctx_ren_extend_fresh_ftv sigma sigma' s0 y r0
                    hctx__UU03c3_0) s3 h5
                  (nc_lam uSort y s3 k sigma' hNC_sub0))) s2) a) x0) b __ __
          __) sigma0 __ __ x1;
     Alpha_app _ _ _ _ _ sigma0 x0 x1 ->
      eq_rec_r r0 (\_ -> false_rec) sigma0 __ __ x0 x1;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ -> false_rec) r1 __ __})
    (\bSort s1 iHs1 s2 iHs2 hNC_s_x0 hNC_s__UU03c3_0 hNC_subs0 r0 hctx__UU03c3_0 _ ha_sub0 hNC_sub0 ->
    case ha_sub0 of {
     Alpha_var _ _ sigma0 x0 -> eq_rec_r r0 (\_ -> false_rec) sigma0 __ __ x0;
     Alpha_lam _ _ _ _ _ _ sigma0 x0 ->
      eq_rec_r r0 (\_ -> false_rec) sigma0 __ __ x0;
     Alpha_app b s3 s4 t1 t2 sigma0 x0 x1 ->
      eq_rec_r r0 (\_ ->
        eq_rec_r bSort (\_ ->
          eq_rec_r (sub x t s1) (\_ ->
            eq_rec_r (sub x t s2) (\_ h4 h5 -> Alpha_app bSort
              (let {
                sub0 x2 u t0 =
                  case t0 of {
                   Tmvar y ->
                    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                           x2 y of {
                     Prelude.True -> u;
                     Prelude.False -> Tmvar y};
                   Tmabs b0 y k1 t' -> Tmabs b0 y k1 (sub0 x2 u t');
                   Tmbin b0 t3 t4 -> Tmbin b0 (sub0 x2 u t3) (sub0 x2 u t4);
                   Tmbuiltin d -> Tmbuiltin d}}
               in sub0 x (psubs sigma t)
                    (let {
                      psubs0 sigma1 t0 =
                        case t0 of {
                         Tmvar x2 ->
                          case lookup x2 sigma1 of {
                           Prelude.Just t3 -> t3;
                           Prelude.Nothing -> Tmvar x2};
                         Tmabs b0 x2 a s0 -> Tmabs b0 x2 a (psubs0 sigma1 s0);
                         Tmbin b0 s0 t3 -> Tmbin b0 (psubs0 sigma1 s0)
                          (psubs0 sigma1 t3);
                         Tmbuiltin d -> Tmbuiltin d}}
                     in psubs0 sigma s1))
              (let {
                psubs0 sigma1 t0 =
                  case t0 of {
                   Tmvar x2 ->
                    case lookup x2 sigma1 of {
                     Prelude.Just t3 -> t3;
                     Prelude.Nothing -> Tmvar x2};
                   Tmabs b0 x2 a s0 -> Tmabs b0 x2 a (psubs0 sigma1 s0);
                   Tmbin b0 s0 t3 -> Tmbin b0 (psubs0 sigma1 s0)
                    (psubs0 sigma1 t3);
                   Tmbuiltin d -> Tmbuiltin d}}
               in psubs0 sigma' s4)
              (let {
                sub0 x2 u t0 =
                  case t0 of {
                   Tmvar y ->
                    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                           x2 y of {
                     Prelude.True -> u;
                     Prelude.False -> Tmvar y};
                   Tmabs b0 y k1 t' -> Tmabs b0 y k1 (sub0 x2 u t');
                   Tmbin b0 t3 t4 -> Tmbin b0 (sub0 x2 u t3) (sub0 x2 u t4);
                   Tmbuiltin d -> Tmbuiltin d}}
               in sub0 x (psubs sigma t)
                    (let {
                      psubs0 sigma1 t0 =
                        case t0 of {
                         Tmvar x2 ->
                          case lookup x2 sigma1 of {
                           Prelude.Just t3 -> t3;
                           Prelude.Nothing -> Tmvar x2};
                         Tmabs b0 x2 a s0 -> Tmabs b0 x2 a (psubs0 sigma1 s0);
                         Tmbin b0 s0 t3 -> Tmbin b0 (psubs0 sigma1 s0)
                          (psubs0 sigma1 t3);
                         Tmbuiltin d -> Tmbuiltin d}}
                     in psubs0 sigma s2))
              (let {
                psubs0 sigma1 t0 =
                  case t0 of {
                   Tmvar x2 ->
                    case lookup x2 sigma1 of {
                     Prelude.Just t3 -> t3;
                     Prelude.Nothing -> Tmvar x2};
                   Tmabs b0 x2 a s0 -> Tmabs b0 x2 a (psubs0 sigma1 s0);
                   Tmbin b0 s0 t3 -> Tmbin b0 (psubs0 sigma1 s0)
                    (psubs0 sigma1 t3);
                   Tmbuiltin d -> Tmbuiltin d}}
               in psubs0 sigma' t2) r0
              (iHs1 (nc_app_l bSort s1 s2 ((:) ((,) x t) ([])) hNC_s_x0)
                (nc_app_l bSort s1 s2 sigma hNC_s__UU03c3_0)
                (nc_app_l bSort (psubs sigma s1)
                  (let {
                    psubs0 sigma1 t0 =
                      case t0 of {
                       Tmvar x2 ->
                        case lookup x2 sigma1 of {
                         Prelude.Just t3 -> t3;
                         Prelude.Nothing -> Tmvar x2};
                       Tmabs b0 x2 a s0 -> Tmabs b0 x2 a (psubs0 sigma1 s0);
                       Tmbin b0 s0 t3 -> Tmbin b0 (psubs0 sigma1 s0)
                        (psubs0 sigma1 t3);
                       Tmbuiltin d -> Tmbuiltin d}}
                   in psubs0 sigma s2) ((:) ((,) x (psubs sigma t)) ([]))
                  hNC_subs0) r0 hctx__UU03c3_0 s4 h4
                (nc_app_l bSort s4 t2 sigma' hNC_sub0))
              (iHs2 (nc_app_r bSort s1 s2 ((:) ((,) x t) ([])) hNC_s_x0)
                (nc_app_r bSort s1 s2 sigma hNC_s__UU03c3_0)
                (nc_app_r bSort
                  (let {
                    psubs0 sigma1 t0 =
                      case t0 of {
                       Tmvar x2 ->
                        case lookup x2 sigma1 of {
                         Prelude.Just t3 -> t3;
                         Prelude.Nothing -> Tmvar x2};
                       Tmabs b0 x2 a s0 -> Tmabs b0 x2 a (psubs0 sigma1 s0);
                       Tmbin b0 s0 t3 -> Tmbin b0 (psubs0 sigma1 s0)
                        (psubs0 sigma1 t3);
                       Tmbuiltin d -> Tmbuiltin d}}
                   in psubs0 sigma s1) (psubs sigma s2) ((:) ((,) x
                  (psubs sigma t)) ([])) hNC_subs0) r0 hctx__UU03c3_0 t2 h5
                (nc_app_r bSort s4 t2 sigma' hNC_sub0))) t1) s3) b __ __)
        sigma0 __ __ x0 x1;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ -> false_rec) r1 __ __})
    (\d _ _ _ r0 _ _ ha_sub0 _ ->
    case ha_sub0 of {
     Alpha_var _ _ sigma0 x0 -> eq_rec_r r0 (\_ -> false_rec) sigma0 __ __ x0;
     Alpha_lam _ _ _ _ _ _ sigma0 x0 ->
      eq_rec_r r0 (\_ -> false_rec) sigma0 __ __ x0;
     Alpha_app _ _ _ _ _ sigma0 x0 x1 ->
      eq_rec_r r0 (\_ -> false_rec) sigma0 __ __ x0 x1;
     Alpha_builtin r1 d0 ->
      eq_rec_r r0 (\_ -> eq_rec_r d (\_ -> Alpha_builtin r0 d) d0) r1 __ __})
    s hNC_s_x hNC_s__UU03c3_ hNC_subs r hctx__UU03c3_ xtsAlpha ha_sub hNC_sub

data Has_kind =
   K_Var (([]) ((,) Prelude.String Kind)) Prelude.String Kind
 | K_Fun (([]) ((,) BinderTyname Kind)) Term0 Term0 Has_kind Has_kind
 | K_IFix (([]) ((,) BinderTyname Kind)) Term0 Term0 Kind Has_kind Has_kind
 | K_Forall (([]) ((,) BinderTyname Kind)) BinderTyname Kind Term0 Has_kind
 | K_Builtin (([]) ((,) BinderTyname Kind)) DefaultUni
 | K_Lam (([]) ((,) BinderTyname Kind)) BinderTyname Kind Term0 Kind 
 Has_kind
 | K_App (([]) ((,) BinderTyname Kind)) Term0 Term0 Kind Kind Has_kind 
 Has_kind

has_kind_rect :: ((([]) ((,) Prelude.String Kind)) -> Prelude.String -> Kind
                 -> () -> a1) -> ((([]) ((,) BinderTyname Kind)) -> Term0 ->
                 Term0 -> Has_kind -> a1 -> Has_kind -> a1 -> a1) -> ((([])
                 ((,) BinderTyname Kind)) -> Term0 -> Term0 -> Kind ->
                 Has_kind -> a1 -> Has_kind -> a1 -> a1) -> ((([])
                 ((,) BinderTyname Kind)) -> BinderTyname -> Kind -> Term0 ->
                 Has_kind -> a1 -> a1) -> ((([]) ((,) BinderTyname Kind)) ->
                 DefaultUni -> () -> a1) -> ((([]) ((,) BinderTyname Kind))
                 -> BinderTyname -> Kind -> Term0 -> Kind -> Has_kind -> a1
                 -> a1) -> ((([]) ((,) BinderTyname Kind)) -> Term0 -> Term0
                 -> Kind -> Kind -> Has_kind -> a1 -> Has_kind -> a1 -> a1)
                 -> (([]) ((,) BinderTyname Kind)) -> Term0 -> Kind ->
                 Has_kind -> a1
has_kind_rect f0 f1 f2 f3 f4 f5 f6 _ _ _ h =
  case h of {
   K_Var _UU0394_ x k -> f0 _UU0394_ x k __;
   K_Fun _UU0394_ t1 t2 h0 h1 ->
    f1 _UU0394_ t1 t2 h0
      (has_kind_rect f0 f1 f2 f3 f4 f5 f6 _UU0394_ t1 Kind_Base h0) h1
      (has_kind_rect f0 f1 f2 f3 f4 f5 f6 _UU0394_ t2 Kind_Base h1);
   K_IFix _UU0394_ f7 t k h0 h1 ->
    f2 _UU0394_ f7 t k h0
      (has_kind_rect f0 f1 f2 f3 f4 f5 f6 _UU0394_ t k h0) h1
      (has_kind_rect f0 f1 f2 f3 f4 f5 f6 _UU0394_ f7 (Kind_Arrow (Kind_Arrow
        k Kind_Base) (Kind_Arrow k Kind_Base)) h1);
   K_Forall _UU0394_ x k t h0 ->
    f3 _UU0394_ x k t h0
      (has_kind_rect f0 f1 f2 f3 f4 f5 f6 ((:) ((,) x k) _UU0394_) t
        Kind_Base h0);
   K_Builtin _UU0394_ t -> f4 _UU0394_ t __;
   K_Lam _UU0394_ x k1 t k2 h0 ->
    f5 _UU0394_ x k1 t k2 h0
      (has_kind_rect f0 f1 f2 f3 f4 f5 f6 ((:) ((,) x k1) _UU0394_) t k2 h0);
   K_App _UU0394_ t1 t2 k1 k2 h0 h1 ->
    f6 _UU0394_ t1 t2 k1 k2 h0
      (has_kind_rect f0 f1 f2 f3 f4 f5 f6 _UU0394_ t1 (Kind_Arrow k1 k2) h0)
      h1 (has_kind_rect f0 f1 f2 f3 f4 f5 f6 _UU0394_ t2 k1 h1)}

data Step_gu =
   Step_gu_intro Term0 Term0 Term0 Alpha GU Step_naive

data Red_gu_na =
   Red_gu_na_star Term0 Term0 Term0 Step_gu Red_gu_na
 | Red_gu_na_nil Term0

red_gu_na_rect :: (Term0 -> Term0 -> Term0 -> Step_gu -> Red_gu_na -> a1 ->
                  a1) -> (Term0 -> a1) -> Term0 -> Term0 -> Red_gu_na -> a1
red_gu_na_rect f0 f1 _ _ r =
  case r of {
   Red_gu_na_star s t t' s0 r0 ->
    f0 s t t' s0 r0 (red_gu_na_rect f0 f1 t t' r0);
   Red_gu_na_nil s -> f1 s}

red_gu_na_rec :: (Term0 -> Term0 -> Term0 -> Step_gu -> Red_gu_na -> a1 ->
                 a1) -> (Term0 -> a1) -> Term0 -> Term0 -> Red_gu_na -> a1
red_gu_na_rec =
  red_gu_na_rect

step_naive_preserves_alpha2 :: Term0 -> Term0 -> Term0 -> (([])
                               ((,) Prelude.String Prelude.String)) -> GU ->
                               GU -> Alpha -> Step_naive -> SigT Term0
                               ((,) Step_naive Alpha)
step_naive_preserves_alpha2 s t s' r x x0 x1 x2 =
  step_naive_rec (\x3 a s0 t0 h _ h0 r0 h1 ->
    case h1 of {
     Alpha_var _ _ sigma x4 -> eq_rec_r r0 (\_ -> false_rec) sigma __ __ x4;
     Alpha_lam _ _ _ _ _ _ sigma x4 ->
      eq_rec_r r0 (\_ -> false_rec) sigma __ __ x4;
     Alpha_app b s1 _ t1 t2 sigma x4 x5 ->
      eq_rec_r r0 (\_ ->
        eq_rec_r App (\_ ->
          eq_rec_r (Tmabs Lam x3 a s0) (\_ ->
            eq_rec_r t0 (\_ h7 h8 ->
              case h7 of {
               Alpha_var _ _ sigma0 x6 ->
                eq_rec_r r0 (\_ -> false_rec) sigma0 __ __ x6;
               Alpha_lam b0 x6 y a0 s2 s3 sigma0 x7 ->
                eq_rec_r r0 (\_ ->
                  eq_rec_r Lam (\_ ->
                    eq_rec_r x3 (\_ ->
                      eq_rec_r a (\_ ->
                        eq_rec_r s0 (\_ h10 -> ExistT (sub y t2 s3) ((,)
                          (Step_beta0 y a s3 t2)
                          (alpha_rename_binder_stronger x3 y s0 t0 t2 r0 s3
                            ((:) ((,) x3 y) r0) h10 h8 StarR
                            (gu_applam_to_nc App Lam s0 t0 x3 a h)
                            (gu_applam_to_nc App Lam s3 t2 y a h0)))) s2) a0)
                      x6) b0 __ __ __) sigma0 __ __ x7;
               Alpha_app _ _ _ _ _ sigma0 x6 x7 ->
                eq_rec_r r0 (\_ -> false_rec) sigma0 __ __ x6 x7;
               Alpha_builtin r1 _ -> eq_rec_r r0 (\_ -> false_rec) r1 __ __})
              t1) s1) b __ __) sigma __ __ x4 x5;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ -> false_rec) r1 __ __})
    (\b s1 s2 t0 _ iHstep_naive h _ h0 r0 h1 ->
    case h1 of {
     Alpha_var _ _ sigma x3 -> eq_rec_r r0 (\_ -> false_rec) sigma __ __ x3;
     Alpha_lam _ _ _ _ _ _ sigma x3 ->
      eq_rec_r r0 (\_ -> false_rec) sigma __ __ x3;
     Alpha_app b0 s3 s4 t1 t2 sigma x3 x4 ->
      eq_rec_r r0 (\_ ->
        eq_rec_r b (\_ ->
          eq_rec_r s1 (\_ ->
            eq_rec_r t0 (\_ h8 h9 ->
              let {
               h3 = iHstep_naive (gu_app_l b s1 t0 h) s4
                      (gu_app_l b s4 t2 h0) r0 h8}
              in
              case h3 of {
               ExistT x5 p ->
                case p of {
                 (,) s0 a -> ExistT (Tmbin b x5 t2) ((,) (Step_appL0 b s4 x5
                  t2 s0) (Alpha_app b s2 x5 t0 t2 r0 a h9))}}) t1) s3) b0 __
          __) sigma __ __ x3 x4;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ -> false_rec) r1 __ __})
    (\b s0 t1 t2 _ iHstep_naive h _ h0 r0 h1 ->
    case h1 of {
     Alpha_var _ _ sigma x3 -> eq_rec_r r0 (\_ -> false_rec) sigma __ __ x3;
     Alpha_lam _ _ _ _ _ _ sigma x3 ->
      eq_rec_r r0 (\_ -> false_rec) sigma __ __ x3;
     Alpha_app b0 s1 s2 t3 t4 sigma x3 x4 ->
      eq_rec_r r0 (\_ ->
        eq_rec_r b (\_ ->
          eq_rec_r s0 (\_ ->
            eq_rec_r t1 (\_ h8 h9 ->
              let {
               h3 = iHstep_naive (gu_app_r b s0 t1 h) t4
                      (gu_app_r b s2 t4 h0) r0 h9}
              in
              case h3 of {
               ExistT x5 p ->
                case p of {
                 (,) s3 a -> ExistT (Tmbin b s2 x5) ((,) (Step_appR0 b s2 t4
                  x5 s3) (Alpha_app b s0 s2 t2 x5 r0 h8 a))}}) t3) s1) b0 __
          __) sigma __ __ x3 x4;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ -> false_rec) r1 __ __})
    (\b x3 a s1 s2 _ iHstep_naive h _ h0 r0 h1 ->
    case h1 of {
     Alpha_var _ _ sigma x4 -> eq_rec_r r0 (\_ -> false_rec) sigma __ __ x4;
     Alpha_lam b0 x4 y a0 s3 s4 sigma x5 ->
      eq_rec_r r0 (\_ ->
        eq_rec_r b (\_ ->
          eq_rec_r x3 (\_ ->
            eq_rec_r a (\_ ->
              eq_rec_r s1 (\_ h9 ->
                let {
                 h2 = iHstep_naive (gu_lam b x3 a s1 h) s4
                        (gu_lam b y a s4 h0) ((:) ((,) x3 y) r0) h9}
                in
                case h2 of {
                 ExistT x6 p ->
                  case p of {
                   (,) s0 a1 -> ExistT (Tmabs b y a x6) ((,) (Step_abs0 b y a
                    s4 x6 s0) (Alpha_lam b x3 y a s2 x6 r0 a1))}}) s3) a0) x4)
          b0 __ __ __) sigma __ __ x5;
     Alpha_app _ _ _ _ _ sigma x4 x5 ->
      eq_rec_r r0 (\_ -> false_rec) sigma __ __ x4 x5;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ -> false_rec) r1 __ __}) s t x2 x
    s' x0 r x1

step_gu_app_l :: BSort -> Term0 -> Term0 -> Term0 -> Step_gu -> SigT 
                 Term0 ((,) Alpha (SigT Term0 ((,) Alpha Step_gu)))
step_gu_app_l b s1 s2 t1 x =
  let {app0 = to_GU (Tmbin b s1 s2)} in
  let {heqapp = to_GU_app_unfold b s1 s2 app0} in
  case heqapp of {
   ExistT x0 s ->
    case s of {
     ExistT x1 p ->
      case p of {
       (,) p0 a ->
        case p0 of {
         (,) _ a0 ->
          case x of {
           Step_gu_intro s0 s' t x2 x3 x4 ->
            eq_rec_r s1 (\_ ->
              eq_rec_r t1 (\h0 h1 h2 ->
                eq_rec_r (Tmbin b x0 x1) (\_ ->
                  let {
                   h3 = step_naive_preserves_alpha2 s' t1 x0 ([]) h1
                          (gu_app_l b x0 x1
                            (eq_rec_r (to_GU (Tmbin b s1 s2))
                              (to_GU__GU (Tmbin b s1 s2)) (Tmbin b x0 x1)))
                          (alpha_extend_ids ([]) s' x0 Id_ctx_nil
                            (alpha_extend_ids ([]) s' x0 Id_ctx_nil
                              (alpha_trans s' s1 x0 ([]) ([]) ([])
                                Alpha_trans_nil
                                (alpha_sym s1 s' (sym_alpha_ctx ([])) ([])
                                  (sym_alpha_ctx_left_is_sym ([])) h0) a0)))
                          h2}
                  in
                  case h3 of {
                   ExistT x5 p1 ->
                    case p1 of {
                     (,) s3 a1 -> ExistT x5 ((,) a1 (ExistT x1 ((,) a
                      (Step_gu_intro (Tmbin b s1 s2) (Tmbin b x0 x1) (Tmbin b
                      x5 x1)
                      (let {_evar_0_ = to_GU__alpha (Tmbin b s1 s2)} in
                       eq_rec_r (to_GU (Tmbin b s1 s2)) _evar_0_ (Tmbin b x0
                         x1))
                      (let {_evar_0_ = to_GU__GU (Tmbin b s1 s2)} in
                       eq_rec_r (to_GU (Tmbin b s1 s2)) _evar_0_ (Tmbin b x0
                         x1)) (Step_appL0 b x0 x5 x1 s3)))))}}) app0 __) t)
              s0 __ x2 x3 x4}}}}}

step_gu_na_lam_fold :: USort -> Prelude.String -> Kind -> Term0 -> Term0 ->
                       Step_gu -> SigT Term0 ((,) Step_gu Alpha)
step_gu_na_lam_fold b x a s s' x0 =
  let {h0 = to_GU__alpha (Tmabs b x a s)} in
  case x0 of {
   Step_gu_intro s0 s'0 t x1 x2 x3 ->
    eq_rec_r s (\_ ->
      eq_rec_r s' (\h1 h2 h3 ->
        case h0 of {
         Alpha_var _ _ sigma x4 ->
          eq_rec_r ([]) (\_ -> false_rec) sigma __ __ x4;
         Alpha_lam b0 x4 y a0 s1 s2 sigma x5 ->
          eq_rec_r ([]) (\_ ->
            eq_rec_r b (\_ ->
              eq_rec_r x (\_ ->
                eq_rec_r a (\_ ->
                  eq_rec_r s (\_ _ ->
                    let {
                     h4 = alpha_trans s'0 s s2 ((:) ((,) x x) ([])) ((:) ((,)
                            x y) ([])) ((:) ((,) x y) ([])) (Alpha_trans_cons
                            x x y ([]) ([]) ([]) Alpha_trans_nil)
                            (alpha_extend_ids ((:) ((,) x x) ([])) s'0 s
                              (Id_ctx_cons x ([]) Id_ctx_nil)
                              (alpha_extend_ids ([]) s'0 s Id_ctx_nil
                                (alpha_extend_ids ([]) s'0 s Id_ctx_nil
                                  (alpha_extend_ids ([]) s'0 s Id_ctx_nil
                                    (alpha_sym s s'0 (sym_alpha_ctx ([]))
                                      ([]) (sym_alpha_ctx_left_is_sym ([]))
                                      h1)))))
                            (let {
                              h4 = eq_rec_r (to_GU (Tmabs b x a s)) h0 (Tmabs
                                     b y a s2)}
                             in
                             case h4 of {
                              Alpha_var _ _ sigma0 x6 ->
                               eq_rec_r ([]) (\_ -> false_rec) sigma0 __ __
                                 x6;
                              Alpha_lam b1 x6 y0 a1 s3 s4 sigma0 x7 ->
                               eq_rec_r ([]) (\_ ->
                                 eq_rec_r b (\_ ->
                                   eq_rec_r x (\_ ->
                                     eq_rec_r a (\_ ->
                                       eq_rec_r s (\_ ->
                                         eq_rec_r y (\_ ->
                                           eq_rec_r s2 (\h7 -> h7) s4) y0 __)
                                         s3) a1) x6) b1 __ __ __) sigma0 __
                                 __ x7;
                              Alpha_app _ _ _ _ _ sigma0 x6 x7 ->
                               eq_rec_r ([]) (\_ -> false_rec) sigma0 __ __
                                 x6 x7;
                              Alpha_builtin r _ ->
                               eq_rec_r ([]) (\_ -> false_rec) r __ __})}
                    in
                    let {
                     h5 = step_naive_preserves_alpha2 s'0 s' s2 ((:) ((,) x
                            y) ([])) h2
                            (let {h5 = to_GU__GU (Tmabs b x a s)} in
                             let {
                              h6 = eq_rec_r (to_GU (Tmabs b x a s)) h5 (Tmabs
                                     b y a s2)}
                             in
                             gu_lam b y a s2 h6) h4 h3}
                    in
                    case h5 of {
                     ExistT x6 p ->
                      case p of {
                       (,) s3 a1 -> ExistT (Tmabs b y a x6) ((,)
                        (Step_gu_intro (Tmabs b x a s) (Tmabs b y a s2)
                        (Tmabs b y a x6)
                        (eq_rec_r (to_GU (Tmabs b x a s)) h0 (Tmabs b y a
                          s2))
                        (let {h6 = to_GU__GU (Tmabs b x a s)} in
                         eq_rec_r (to_GU (Tmabs b x a s)) h6 (Tmabs b y a s2))
                        (Step_abs0 b y a s2 x6 s3))
                        (alpha_sym (Tmabs b x a s') (Tmabs b y a x6) ([])
                          ([]) Alpha_sym_nil (Alpha_lam b x y a s' x6 ([])
                          a1)))}}) s1) a0) x4) b0 __ __ __) sigma __ __ x5;
         Alpha_app _ _ _ _ _ sigma x4 x5 ->
          eq_rec_r ([]) (\_ -> false_rec) sigma __ __ x4 x5;
         Alpha_builtin r _ -> eq_rec_r ([]) (\_ -> false_rec) r __ __}) t) s0
      __ x1 x2 x3}

step_gu_preserves_alpha :: Term0 -> Term0 -> Term0 -> (([])
                           ((,) Prelude.String Prelude.String)) -> Alpha ->
                           Step_gu -> SigT Term0 ((,) Step_gu Alpha)
step_gu_preserves_alpha s s' t r x x0 =
  case x0 of {
   Step_gu_intro s0 s'0 t0 x1 x2 x3 ->
    eq_rec_r s (\_ ->
      eq_rec_r s' (\h1 h2 h3 ->
        let {
         h4 = step_naive_preserves_alpha2 s'0 s' (to_GU t) r h2 (to_GU__GU t)
                (alpha_trans s'0 s (to_GU t) (ctx_id_left r) r r
                  (id_left_trans r)
                  (alpha_extend_ids (ctx_id_left r) s'0 s
                    (ctx_id_left_is_id r)
                    (alpha_sym s s'0 ([]) ([]) Alpha_sym_nil h1))
                  (alpha_trans s t (to_GU t) r (ctx_id_right r) r
                    (id_right_trans r) x
                    (alpha_extend_ids (ctx_id_right r) t (to_GU t)
                      (ctx_id_right_is_id r) (to_GU__alpha t)))) h3}
        in
        case h4 of {
         ExistT x4 p ->
          case p of {
           (,) s1 a -> ExistT x4 ((,) (Step_gu_intro t (to_GU t) x4
            (to_GU__alpha t) (to_GU__GU t) s1) a)}}) t0) s0 __ x1 x2 x3}

red_gu_naive_preserves_alpha :: Term0 -> Term0 -> Term0 -> (([])
                                ((,) Prelude.String Prelude.String)) -> Alpha
                                -> Red_gu_na -> SigT Term0
                                ((,) Red_gu_na Alpha)
red_gu_naive_preserves_alpha s s' t r x x0 =
  red_gu_na_rec (\s0 t0 _ s1 _ iHred_gu_na t1 r0 h ->
    let {s2 = step_gu_preserves_alpha s0 t0 t1 r0 h s1} in
    case s2 of {
     ExistT x1 p ->
      case p of {
       (,) s3 a ->
        let {iHred_gu_na0 = iHred_gu_na x1 r0 a} in
        case iHred_gu_na0 of {
         ExistT x2 p0 ->
          case p0 of {
           (,) r1 a0 -> ExistT x2 ((,) (Red_gu_na_star t1 x1 x2 s3 r1) a0)}}}})
    (\_ t0 _ h -> ExistT t0 ((,) (Red_gu_na_nil t0) h)) s s' x0 t r x

red_gu_na_lam_fold :: USort -> Prelude.String -> Kind -> Term0 -> Term0 ->
                      Red_gu_na -> SigT Term0 ((,) Red_gu_na Alpha)
red_gu_na_lam_fold b x a s s' x0 =
  red_gu_na_rec (\s0 t t' s1 _ iHred_gu_na ->
    case iHred_gu_na of {
     ExistT x1 p ->
      case p of {
       (,) r a0 ->
        let {s2 = step_gu_na_lam_fold b x a s0 t s1} in
        case s2 of {
         ExistT x2 p0 ->
          case p0 of {
           (,) s3 a1 ->
            let {
             h0 = red_gu_naive_preserves_alpha (Tmabs b x a t) x1 x2 ([])
                    (alpha_extend_ids ([]) (Tmabs b x a t) x2 Id_ctx_nil
                      (alpha_extend_ids ([]) (Tmabs b x a t) x2 Id_ctx_nil
                        (alpha_extend_ids ([]) (Tmabs b x a t) x2 Id_ctx_nil
                          (alpha_sym x2 (Tmabs b x a t) (sym_alpha_ctx ([]))
                            ([]) (sym_alpha_ctx_left_is_sym ([])) a1)))) r}
            in
            case h0 of {
             ExistT x3 p1 ->
              case p1 of {
               (,) r0 a2 -> ExistT x3 ((,) (Red_gu_na_star (Tmabs b x a s0)
                x2 x3 s3 r0)
                (alpha_extend_ids ([]) x3 (Tmabs b x a t') Id_ctx_nil
                  (alpha_extend_ids ([]) x3 (Tmabs b x a t') Id_ctx_nil
                    (alpha_trans x3 x1 (Tmabs b x a t') ([]) ([]) ([])
                      Alpha_trans_nil
                      (alpha_sym x1 x3 (sym_alpha_ctx ([])) ([])
                        (sym_alpha_ctx_left_is_sym ([])) a2) a0))))}}}}}})
    (\s0 -> ExistT (Tmabs b x a s0) ((,) (Red_gu_na_nil (Tmabs b x a s0))
    (alpha_refl (Tmabs b x a s0) ([]) Alpha_refl_nil))) s s' x0

step_gu_na_appl_fold :: BSort -> Term0 -> Term0 -> Term0 -> Step_gu -> SigT
                        Term0 ((,) Step_gu Alpha)
step_gu_na_appl_fold b s1 s2 t1 hstep_gu =
  case hstep_gu of {
   Step_gu_intro s s' t x x0 x1 ->
    eq_rec_r s1 (\_ ->
      eq_rec_r s2 (\h h0 h1 ->
        let {hgu_a = to_GU__alpha (Tmbin b s1 t1)} in
        case hgu_a of {
         Alpha_var _ _ sigma x2 ->
          eq_rec_r ([]) (\_ -> false_rec) sigma __ __ x2;
         Alpha_lam _ _ _ _ _ _ sigma x2 ->
          eq_rec_r ([]) (\_ -> false_rec) sigma __ __ x2;
         Alpha_app b0 s3 s4 t2 t3 sigma x2 x3 ->
          eq_rec_r ([]) (\_ ->
            eq_rec_r b (\_ ->
              eq_rec_r s1 (\_ ->
                eq_rec_r t1 (\_ h5 h8 ->
                  let {
                   hstep_na' = step_naive_preserves_alpha2 s' s2 s4 ([]) h0
                                 (let {hgu_app = to_GU__GU (Tmbin b s1 t1)}
                                  in
                                  let {
                                   hgu_app0 = eq_rec_r
                                                (to_GU (Tmbin b s1 t1))
                                                hgu_app (Tmbin b s4 t3)}
                                  in
                                  gu_app_l b s4 t3 hgu_app0)
                                 (alpha_extend_ids ([]) s' s4 Id_ctx_nil
                                   (alpha_extend_ids ([]) s' s4 Id_ctx_nil
                                     (alpha_trans s' s1 s4 ([]) ([]) ([])
                                       Alpha_trans_nil
                                       (alpha_sym s1 s' (sym_alpha_ctx ([]))
                                         ([])
                                         (sym_alpha_ctx_left_is_sym ([])) h)
                                       h5))) h1}
                  in
                  case hstep_na' of {
                   ExistT x4 p ->
                    case p of {
                     (,) s0 a -> ExistT (Tmbin b x4 t3) ((,) (Step_gu_intro
                      (Tmbin b s1 t1) (Tmbin b s4 t3) (Tmbin b x4 t3)
                      (eq_rec_r (to_GU (Tmbin b s1 t1)) hgu_a (Tmbin b s4
                        t3))
                      (let {_evar_0_ = to_GU__GU (Tmbin b s1 t1)} in
                       eq_rec_r (to_GU (Tmbin b s1 t1)) _evar_0_ (Tmbin b s4
                         t3)) (Step_appL0 b s4 x4 t3 s0)) (Alpha_app b x4 s2
                      t3 t1 ([])
                      (alpha_extend_ids ([]) x4 s2 Id_ctx_nil
                        (alpha_extend_ids ([]) x4 s2 Id_ctx_nil
                          (alpha_extend_ids ([]) x4 s2 Id_ctx_nil
                            (alpha_sym s2 x4 (sym_alpha_ctx ([])) ([])
                              (sym_alpha_ctx_left_is_sym ([])) a))))
                      (alpha_extend_ids ([]) t3 t1 Id_ctx_nil
                        (alpha_extend_ids ([]) t3 t1 Id_ctx_nil
                          (alpha_extend_ids ([]) t3 t1 Id_ctx_nil
                            (alpha_sym t1 t3 (sym_alpha_ctx ([])) ([])
                              (sym_alpha_ctx_left_is_sym ([])) h8))))))}}) t2)
                s3) b0 __ __) sigma __ __ x2 x3;
         Alpha_builtin r _ -> eq_rec_r ([]) (\_ -> false_rec) r __ __}) t) s
      __ x x0 x1}

step_gu_na_appr_fold :: BSort -> Term0 -> Term0 -> Term0 -> Step_gu -> SigT
                        Term0 ((,) Step_gu Alpha)
step_gu_na_appr_fold b s1 t1 t2 hstep_gu =
  case hstep_gu of {
   Step_gu_intro s s' t x x0 x1 ->
    eq_rec_r t1 (\_ ->
      eq_rec_r t2 (\h h0 h1 ->
        let {hgu_a = to_GU__alpha (Tmbin b s1 t1)} in
        case hgu_a of {
         Alpha_var _ _ sigma x2 ->
          eq_rec_r ([]) (\_ -> false_rec) sigma __ __ x2;
         Alpha_lam _ _ _ _ _ _ sigma x2 ->
          eq_rec_r ([]) (\_ -> false_rec) sigma __ __ x2;
         Alpha_app b0 s2 s3 t3 t4 sigma x2 x3 ->
          eq_rec_r ([]) (\_ ->
            eq_rec_r b (\_ ->
              eq_rec_r s1 (\_ ->
                eq_rec_r t1 (\_ h5 h8 ->
                  let {
                   hstep_na' = step_naive_preserves_alpha2 s' t2 t4 ([]) h0
                                 (let {hgu_app = to_GU__GU (Tmbin b s1 t1)}
                                  in
                                  let {
                                   hgu_app0 = eq_rec_r
                                                (to_GU (Tmbin b s1 t1))
                                                hgu_app (Tmbin b s3 t4)}
                                  in
                                  gu_app_r b s3 t4 hgu_app0)
                                 (alpha_extend_ids ([]) s' t4 Id_ctx_nil
                                   (alpha_extend_ids ([]) s' t4 Id_ctx_nil
                                     (alpha_trans s' t1 t4 ([]) ([]) ([])
                                       Alpha_trans_nil
                                       (alpha_sym t1 s' (sym_alpha_ctx ([]))
                                         ([])
                                         (sym_alpha_ctx_left_is_sym ([])) h)
                                       h8))) h1}
                  in
                  case hstep_na' of {
                   ExistT x4 p ->
                    case p of {
                     (,) s0 a -> ExistT (Tmbin b s3 x4) ((,) (Step_gu_intro
                      (Tmbin b s1 t1) (Tmbin b s3 t4) (Tmbin b s3 x4)
                      (eq_rec_r (to_GU (Tmbin b s1 t1)) hgu_a (Tmbin b s3
                        t4))
                      (let {_evar_0_ = to_GU__GU (Tmbin b s1 t1)} in
                       eq_rec_r (to_GU (Tmbin b s1 t1)) _evar_0_ (Tmbin b s3
                         t4)) (Step_appR0 b s3 t4 x4 s0)) (Alpha_app b s3 s1
                      x4 t2 ([])
                      (alpha_extend_ids ([]) s3 s1 Id_ctx_nil
                        (alpha_extend_ids ([]) s3 s1 Id_ctx_nil
                          (alpha_extend_ids ([]) s3 s1 Id_ctx_nil
                            (alpha_sym s1 s3 (sym_alpha_ctx ([])) ([])
                              (sym_alpha_ctx_left_is_sym ([])) h5))))
                      (alpha_extend_ids ([]) x4 t2 Id_ctx_nil
                        (alpha_extend_ids ([]) x4 t2 Id_ctx_nil
                          (alpha_extend_ids ([]) x4 t2 Id_ctx_nil
                            (alpha_sym t2 x4 (sym_alpha_ctx ([])) ([])
                              (sym_alpha_ctx_left_is_sym ([])) a))))))}}) t3)
                s2) b0 __ __) sigma __ __ x2 x3;
         Alpha_builtin r _ -> eq_rec_r ([]) (\_ -> false_rec) r __ __}) t) s
      __ x x0 x1}

red_gu_na_trans :: Term0 -> Term0 -> Term0 -> Red_gu_na -> Red_gu_na ->
                   Red_gu_na
red_gu_na_trans s t u x x0 =
  red_gu_na_rec (\s0 t0 t' s1 h iHred_gu_na u0 h0 ->
    red_gu_na_rec (\s2 t1 _ s3 _ iHred_gu_na0 t2 _ iHred_gu_na1 s4 s5 ->
      iHred_gu_na0 t2
        (iHred_gu_na1 t1 (Red_gu_na_star s2 t1 t1 s3 (Red_gu_na_nil t1)))
        (\u1 h1 -> iHred_gu_na1 u1 (Red_gu_na_star s2 t1 u1 s3 h1)) s4 s5)
      (\s2 t1 h1 _ s3 s4 -> Red_gu_na_star s3 t1 s2 s4 h1) t' u0 h0 t0 h
      iHred_gu_na s0 s1) (\s0 u0 h0 ->
    red_gu_na_rec (\s1 t0 t' s2 _ iHred_gu_na -> Red_gu_na_star s1 t0 t' s2
      iHred_gu_na) (\s1 -> Red_gu_na_nil s1) s0 u0 h0) s t x u x0

red_gu_na_appl_fold :: BSort -> Term0 -> Term0 -> Term0 -> Red_gu_na -> SigT
                       Term0 ((,) Red_gu_na Alpha)
red_gu_na_appl_fold b s1 s2 t h0 =
  red_gu_na_rec (\s t0 t' s0 _ iHred_gu_na ->
    case iHred_gu_na of {
     ExistT x p ->
      case p of {
       (,) r a ->
        let {s3 = step_gu_na_appl_fold b s t0 t s0} in
        case s3 of {
         ExistT x0 p0 ->
          case p0 of {
           (,) s4 a0 ->
            let {
             h = red_gu_naive_preserves_alpha (Tmbin b t0 t) x x0 ([])
                   (alpha_extend_ids ([]) (Tmbin b t0 t) x0 Id_ctx_nil
                     (alpha_extend_ids ([]) (Tmbin b t0 t) x0 Id_ctx_nil
                       (alpha_extend_ids ([]) (Tmbin b t0 t) x0 Id_ctx_nil
                         (alpha_sym x0 (Tmbin b t0 t) (sym_alpha_ctx ([]))
                           ([]) (sym_alpha_ctx_left_is_sym ([])) a0)))) r}
            in
            case h of {
             ExistT x1 p1 ->
              case p1 of {
               (,) r0 a1 -> ExistT x1 ((,) (Red_gu_na_star (Tmbin b s t) x0
                x1 s4 r0)
                (alpha_extend_ids ([]) x1 (Tmbin b t' t) Id_ctx_nil
                  (alpha_extend_ids ([]) x1 (Tmbin b t' t) Id_ctx_nil
                    (alpha_trans x1 x (Tmbin b t' t) ([]) ([]) ([])
                      Alpha_trans_nil
                      (alpha_sym x x1 (sym_alpha_ctx ([])) ([])
                        (sym_alpha_ctx_left_is_sym ([])) a1) a))))}}}}}})
    (\s -> ExistT (Tmbin b s t) ((,) (Red_gu_na_nil (Tmbin b s t))
    (alpha_refl (Tmbin b s t) ([]) Alpha_refl_nil))) s1 s2 h0

red_gu_na_appr_fold :: BSort -> Term0 -> Term0 -> Term0 -> Red_gu_na -> SigT
                       Term0 ((,) Red_gu_na Alpha)
red_gu_na_appr_fold b s1 t1 t2 h0 =
  red_gu_na_rec (\s t t' s0 _ iHred_gu_na ->
    case iHred_gu_na of {
     ExistT x p ->
      case p of {
       (,) r a ->
        let {s2 = step_gu_na_appr_fold b s1 s t s0} in
        case s2 of {
         ExistT x0 p0 ->
          case p0 of {
           (,) s3 a0 ->
            let {
             h = red_gu_naive_preserves_alpha (Tmbin b s1 t) x x0 ([])
                   (alpha_extend_ids ([]) (Tmbin b s1 t) x0 Id_ctx_nil
                     (alpha_extend_ids ([]) (Tmbin b s1 t) x0 Id_ctx_nil
                       (alpha_extend_ids ([]) (Tmbin b s1 t) x0 Id_ctx_nil
                         (alpha_sym x0 (Tmbin b s1 t) (sym_alpha_ctx ([]))
                           ([]) (sym_alpha_ctx_left_is_sym ([])) a0)))) r}
            in
            case h of {
             ExistT x1 p1 ->
              case p1 of {
               (,) r0 a1 -> ExistT x1 ((,) (Red_gu_na_star (Tmbin b s1 s) x0
                x1 s3 r0)
                (alpha_extend_ids ([]) x1 (Tmbin b s1 t') Id_ctx_nil
                  (alpha_extend_ids ([]) x1 (Tmbin b s1 t') Id_ctx_nil
                    (alpha_trans x1 x (Tmbin b s1 t') ([]) ([]) ([])
                      Alpha_trans_nil
                      (alpha_sym x x1 (sym_alpha_ctx ([])) ([])
                        (sym_alpha_ctx_left_is_sym ([])) a1) a))))}}}}}})
    (\s -> ExistT (Tmbin b s1 s) ((,) (Red_gu_na_nil (Tmbin b s1 s))
    (alpha_refl (Tmbin b s1 s) ([]) Alpha_refl_nil))) t1 t2 h0

red_gu_na_app_fold :: BSort -> Term0 -> Term0 -> Term0 -> Term0 -> Red_gu_na
                      -> Red_gu_na -> SigT Term0 ((,) Red_gu_na Alpha)
red_gu_na_app_fold b s1 s2 t1 t2 x x0 =
  let {h = red_gu_na_appl_fold b s1 s2 t1 x} in
  case h of {
   ExistT x1 p ->
    case p of {
     (,) r a ->
      let {h0 = red_gu_na_appr_fold b s2 t1 t2 x0} in
      case h0 of {
       ExistT x2 p0 ->
        case p0 of {
         (,) r0 a0 ->
          let {
           h1 = red_gu_naive_preserves_alpha (Tmbin b s2 t1) x2 x1 ([])
                  (alpha_extend_ids ([]) (Tmbin b s2 t1) x1 Id_ctx_nil
                    (alpha_extend_ids ([]) (Tmbin b s2 t1) x1 Id_ctx_nil
                      (alpha_extend_ids ([]) (Tmbin b s2 t1) x1 Id_ctx_nil
                        (alpha_sym x1 (Tmbin b s2 t1) (sym_alpha_ctx ([]))
                          ([]) (sym_alpha_ctx_left_is_sym ([])) a)))) r0}
          in
          case h1 of {
           ExistT x3 p1 ->
            case p1 of {
             (,) r1 a1 -> ExistT x3 ((,)
              (red_gu_na_trans (Tmbin b s1 t1) x1 x3 r r1)
              (alpha_extend_ids ([]) x3 (Tmbin b s2 t2) Id_ctx_nil
                (alpha_extend_ids ([]) x3 (Tmbin b s2 t2) Id_ctx_nil
                  (alpha_trans x3 x2 (Tmbin b s2 t2) ([]) ([]) ([])
                    Alpha_trans_nil
                    (alpha_sym x2 x3 (sym_alpha_ctx ([])) ([])
                      (sym_alpha_ctx_left_is_sym ([])) a1) a0))))}}}}}}

alpha_preserves_typing :: (([]) ((,) Prelude.String Prelude.String)) -> Term0
                          -> Term0 -> Kind -> (([])
                          ((,) Prelude.String Kind)) -> (([])
                          ((,) Prelude.String Kind)) -> Alpha -> Has_kind ->
                          Has_kind
alpha_preserves_typing sigma s t a gamma gamma' hAlpha =
  alpha_rec (\x y _ _ gamma'0 gamma0 _ a0 hType ->
    case hType of {
     K_Var _UU0394_ x0 k ->
      eq_rec_r gamma0 (\_ ->
        eq_rec_r x (\_ -> eq_rec_r a0 (\_ -> K_Var gamma'0 y a0) k) x0)
        _UU0394_ __ __ __;
     K_Fun _UU0394_ _ _ x0 x1 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0 x1;
     K_IFix _UU0394_ _ _ _ x0 x1 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0 x1;
     K_Forall _UU0394_ _ _ _ x0 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0;
     K_Builtin _UU0394_ _ ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ __;
     K_Lam _UU0394_ _ _ _ _ x0 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0;
     K_App _UU0394_ _ _ _ _ x0 x1 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0 x1})
    (\_ x y a0 s1 s2 _ _ iHHAlpha gamma'0 gamma0 _ _ hType ->
    case hType of {
     K_Var _UU0394_ _ _ ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ __;
     K_Fun _UU0394_ _ _ x0 x1 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0 x1;
     K_IFix _UU0394_ _ _ _ x0 x1 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0 x1;
     K_Forall _UU0394_ x0 k t0 x1 ->
      eq_rec_r gamma0 (\_ ->
        eq_rec_r x (\_ ->
          eq_rec_r a0 (\_ ->
            eq_rec_r s1 (\_ h5 ->
              let {
               iHHAlpha0 = iHHAlpha ((:) ((,) y a0) gamma'0) ((:) ((,) x a0)
                             gamma0) __ Kind_Base h5}
              in
              K_Forall gamma'0 y a0 s2 iHHAlpha0) t0) k) x0 __ __) _UU0394_
        __ __ x1;
     K_Builtin _UU0394_ _ ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ __;
     K_Lam _UU0394_ x0 k1 t0 k2 x1 ->
      eq_rec_r gamma0 (\_ ->
        eq_rec_r x (\_ ->
          eq_rec_r a0 (\_ ->
            eq_rec_r s1 (\_ h5 ->
              let {
               iHHAlpha0 = iHHAlpha ((:) ((,) y a0) gamma'0) ((:) ((,) x a0)
                             gamma0) __ k2 h5}
              in
              K_Lam gamma'0 y a0 s2 k2 iHHAlpha0) t0) k1) x0 __ __) _UU0394_
        __ __ x1;
     K_App _UU0394_ _ _ _ _ x0 x1 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0 x1})
    (\_ s1 s2 t1 t2 _ _ iHHAlpha1 _ iHHAlpha2 gamma'0 gamma0 _ a0 hType ->
    case hType of {
     K_Var _UU0394_ _ _ ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ __;
     K_Fun _UU0394_ t3 t4 x x0 ->
      eq_rec_r gamma0 (\_ ->
        eq_rec_r s1 (\_ ->
          eq_rec_r t1 (\_ h4 h5 -> K_Fun gamma'0 s2 t2
            (iHHAlpha1 gamma'0 gamma0 __ Kind_Base h4)
            (iHHAlpha2 gamma'0 gamma0 __ Kind_Base h5)) t4) t3 __) _UU0394_
        __ __ x x0;
     K_IFix _UU0394_ f0 t0 k x x0 ->
      eq_rec_r gamma0 (\_ ->
        eq_rec_r s1 (\_ ->
          eq_rec_r t1 (\_ h4 h5 -> K_IFix gamma'0 s2 t2 k
            (iHHAlpha2 gamma'0 gamma0 __ k h4)
            (iHHAlpha1 gamma'0 gamma0 __ (Kind_Arrow (Kind_Arrow k Kind_Base)
              (Kind_Arrow k Kind_Base)) h5)) t0) f0 __) _UU0394_ __ __ x x0;
     K_Forall _UU0394_ _ _ _ x ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x;
     K_Builtin _UU0394_ _ ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ __;
     K_Lam _UU0394_ _ _ _ _ x ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x;
     K_App _UU0394_ t3 t4 k1 k2 x x0 ->
      eq_rec_r gamma0 (\_ ->
        eq_rec_r s1 (\_ ->
          eq_rec_r t1 (\_ ->
            eq_rec_r a0 (\h4 h5 -> K_App gamma'0 s2 t2 k1 a0
              (iHHAlpha1 gamma'0 gamma0 __ (Kind_Arrow k1 a0) h4)
              (iHHAlpha2 gamma'0 gamma0 __ k1 h5)) k2) t4) t3 __) _UU0394_ __
        __ x x0}) (\_ d gamma'0 gamma0 _ _ x ->
    case x of {
     K_Var _UU0394_ _ _ ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ __;
     K_Fun _UU0394_ _ _ x0 x1 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0 x1;
     K_IFix _UU0394_ _ _ _ x0 x1 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0 x1;
     K_Forall _UU0394_ _ _ _ x0 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0;
     K_Builtin _UU0394_ t0 ->
      eq_rec_r gamma0 (\_ -> eq_rec_r d (\_ _ -> K_Builtin gamma'0 d) t0)
        _UU0394_ __ __ __;
     K_Lam _UU0394_ _ _ _ _ x0 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0;
     K_App _UU0394_ _ _ _ _ x0 x1 ->
      eq_rec_r gamma0 (\_ -> false_rec) _UU0394_ __ __ x0 x1}) sigma s t
    hAlpha gamma' gamma __ a

substituteTCA_vacuous :: (([]) ((,) Prelude.String Prelude.String)) ->
                         Prelude.String -> Term0 -> Term0 -> Term0 -> Alpha
                         -> Alpha
substituteTCA_vacuous r x u t t' x0 =
  term_rec (\s r0 _ h _ ->
    case h of {
     Alpha_var x1 y sigma x2 ->
      eq_rec_r r0 (\_ _ ->
        eq_rec_r s (\_ ->
          eq_rec_r
            (case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                    x x1 of {
              Prelude.True -> u;
              Prelude.False -> Tmvar x1})
            (eq_rec_r Prelude.False h
              (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                x x1)) (substituteTCA0 x u (Tmvar x1))) y) sigma __ __ x2;
     Alpha_lam _ _ _ _ _ _ sigma x1 ->
      eq_rec_r r0 (\_ _ -> false_rec) sigma __ __ x1;
     Alpha_app _ _ _ _ _ sigma x1 x2 ->
      eq_rec_r r0 (\_ _ -> false_rec) sigma __ __ x1 x2;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ _ -> false_rec) r1 __ __})
    (\uSort s k t'0 iHT' r0 _ h _ ->
    case h of {
     Alpha_var _ _ sigma x1 -> eq_rec_r r0 (\_ _ -> false_rec) sigma __ __ x1;
     Alpha_lam b x1 y a s1 s2 sigma x2 ->
      eq_rec_r r0 (\_ _ ->
        eq_rec_r uSort (\_ ->
          eq_rec_r s (\_ ->
            eq_rec_r k (\_ ->
              eq_rec_r t'0 (\h4 ->
                eq_rec_r uSort (\_ h0 ->
                  eq_rec_r k (\_ _ ->
                    eq_rec_r
                      (case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                              x x1 of {
                        Prelude.True -> Tmabs uSort x1 k s1;
                        Prelude.False ->
                         case existsb
                                (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                  x1) (ftv0 u) of {
                          Prelude.True ->
                           let {y' = fresh2 ((:) ((,) x u) ([])) s1} in
                           let {t'1 = rename0 x1 y' s1} in
                           Tmabs uSort y' k (substituteTCA0 x u t'1);
                          Prelude.False -> Tmabs uSort x1 k
                           (substituteTCA0 x u s1)}})
                      (let {
                        b0 = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                               x x1}
                       in
                       case b0 of {
                        Prelude.True ->
                         eq_rec_r x1 (\_ _ -> Alpha_lam uSort x1 s k s1 t'0
                           r0 h4) x iHT' __;
                        Prelude.False ->
                         let {
                          b1 = existsb
                                 (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                   x1) (ftv0 u)}
                         in
                         case b1 of {
                          Prelude.True ->
                           let {y0 = fresh2 ((:) ((,) x u) ([])) s1} in
                           Alpha_lam uSort y0 s k
                           (substituteTCA0 x u (rename0 x1 y0 s1)) t'0 r0
                           (iHT' ((:) ((,) y0 s) r0) (rename0 x1 y0 s1)
                             (alpha_trans_rename_left s1 t'0 y0 x1 s r0 ((:)
                               ((,) x u) ([])) h4) __);
                          Prelude.False -> Alpha_lam uSort x1 s k
                           (substituteTCA0 x u s1) t'0 r0
                           (iHT' ((:) ((,) x1 s) r0) s1 h4 __)}})
                      (substituteTCA0 x u (Tmabs uSort x1 k s1))) a h0 __) b
                  __ h) s2) a) y) b __ __ __) sigma __ __ x2;
     Alpha_app _ _ _ _ _ sigma x1 x2 ->
      eq_rec_r r0 (\_ _ -> false_rec) sigma __ __ x1 x2;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ _ -> false_rec) r1 __ __})
    (\bSort t'1 iHT'1 t'2 iHT'2 r0 _ h _ ->
    case h of {
     Alpha_var _ _ sigma x1 -> eq_rec_r r0 (\_ _ -> false_rec) sigma __ __ x1;
     Alpha_lam _ _ _ _ _ _ sigma x1 ->
      eq_rec_r r0 (\_ _ -> false_rec) sigma __ __ x1;
     Alpha_app b s1 s2 t1 t2 sigma x1 x2 ->
      eq_rec_r r0 (\_ _ ->
        eq_rec_r bSort (\_ ->
          eq_rec_r t'1 (\_ ->
            eq_rec_r t'2 (\h5 h7 ->
              eq_rec_r bSort (\_ _ ->
                eq_rec_r (Tmbin bSort (substituteTCA0 x u s1)
                  (substituteTCA0 x u t1)) (Alpha_app bSort
                  (substituteTCA0 x u s1) t'1 (substituteTCA0 x u t1) t'2 r0
                  (iHT'1 r0 s1 h5 __) (iHT'2 r0 t1 h7 __))
                  (substituteTCA0 x u (Tmbin bSort s1 t1))) b __ h) t2) s2) b
          __ __) sigma __ __ x1 x2;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ _ -> false_rec) r1 __ __})
    (\d r0 _ h _ ->
    case h of {
     Alpha_var _ _ sigma x1 -> eq_rec_r r0 (\_ _ -> false_rec) sigma __ __ x1;
     Alpha_lam _ _ _ _ _ _ sigma x1 ->
      eq_rec_r r0 (\_ _ -> false_rec) sigma __ __ x1;
     Alpha_app _ _ _ _ _ sigma x1 x2 ->
      eq_rec_r r0 (\_ _ -> false_rec) sigma __ __ x1 x2;
     Alpha_builtin r1 d0 ->
      eq_rec_r r0 (\_ _ ->
        eq_rec_r d
          (eq_rec_r d (\_ h0 ->
            eq_rec_r (Tmbuiltin d) h0 (substituteTCA0 x u (Tmbuiltin d))) d0
            __ h) d0) r1 __ __}) t' r t x0 __

data IdSubst =
   Id_subst_nil
 | Id_subst_cons Prelude.String (([]) ((,) Prelude.String Term0)) IdSubst

id_subst :: (([]) ((,) Prelude.String Kind)) -> ([])
            ((,) Prelude.String Term0)
id_subst e =
  case e of {
   ([]) -> ([]);
   (:) p e' -> case p of {
                (,) x _ -> (:) ((,) x (Tmvar x)) (id_subst e')}}

id_subst_is_IdSubst :: (([]) ((,) Prelude.String Kind)) -> IdSubst
id_subst_is_IdSubst e =
  list_rec Id_subst_nil (\a e0 iHE ->
    case a of {
     (,) s _ -> Id_subst_cons s (id_subst e0) iHE}) e

id_subst__ParSeq :: (([]) ((,) Prelude.String Term0)) -> IdSubst -> ParSeq
id_subst__ParSeq _UU03c3_ x =
  list_rec (\_ -> ParSeq_nil) (\a _UU03c3_0 iH_UU03c3_ h ->
    case a of {
     (,) s t -> ParSeq_cons s t _UU03c3_0
      (iH_UU03c3_
        (case h of {
          Id_subst_nil -> false_rec;
          Id_subst_cons x0 sigma x1 ->
           eq_rec_r s (\_ _ -> eq_rec_r _UU03c3_0 (\h1 -> h1) sigma) x0 __ __
             x1}))}) _UU03c3_ x

data Sn x e =
   SNI (x -> e -> Sn x e)

sn_rect :: (a1 -> (a1 -> a2 -> Sn a1 a2) -> (a1 -> a2 -> a3) -> a3) -> a1 ->
           (Sn a1 a2) -> a3
sn_rect f0 x s =
  case s of {
   SNI s0 -> f0 x s0 (\y y0 -> sn_rect f0 y (s0 y y0))}

sn_rec :: (a1 -> (a1 -> a2 -> Sn a1 a2) -> (a1 -> a2 -> a3) -> a3) -> a1 ->
          (Sn a1 a2) -> a3
sn_rec =
  sn_rect

_UU03b1__preserves_SN_R :: Term0 -> Term0 -> (([])
                           ((,) Prelude.String Prelude.String)) -> Alpha ->
                           (Sn Term0 Step_gu) -> Sn Term0 Step_gu
_UU03b1__preserves_SN_R s s' r h_UU03b1_ hsn =
  sn_rect (\x _ x0 s'0 r0 h_UU03b1_0 -> SNI (\y1 hstep ->
    let {
     h_UU03b1_1 = alpha_sym x s'0 r0 (sym_alpha_ctx r0)
                    (sym_alpha_ctx_is_sym r0) h_UU03b1_0}
    in
    let {
     hstep0 = step_gu_preserves_alpha s'0 y1 x (sym_alpha_ctx r0) h_UU03b1_1
                hstep}
    in
    case hstep0 of {
     ExistT x1 p ->
      case p of {
       (,) s0 a ->
        x0 x1 s0 y1 r0
          (alpha_sym y1 x1 (sym_alpha_ctx r0) r0
            (sym_alpha_ctx_left_is_sym r0) a)}})) s hsn s' r h_UU03b1_

sn_preimage__UU03b1_' :: (Term0 -> Term0) -> Term0 -> Term0 -> (Term0 ->
                         Term0 -> Step_gu -> SigT Term0 ((,) Step_gu Alpha))
                         -> (Sn Term0 Step_gu) -> Alpha -> Sn Term0 Step_gu
sn_preimage__UU03b1_' h x v a b halpha =
  sn_rect (\x0 _ x1 x2 h0 a0 ha -> SNI (\y c ->
    let {c0 = a0 x2 y c} in
    case c0 of {
     ExistT x3 p ->
      case p of {
       (,) s a1 ->
        let {
         ehy = step_gu_preserves_alpha (h0 x2) x3 x0 (sym_alpha_ctx ([]))
                 (alpha_extend_ids (sym_alpha_ctx ([])) (h0 x2) x0 Id_ctx_nil
                   (alpha_extend_ids ([]) (h0 x2) x0 Id_ctx_nil
                     (alpha_extend_ids ([]) (h0 x2) x0 Id_ctx_nil
                       (alpha_sym x0 (h0 x2) (sym_alpha_ctx ([])) ([])
                         (sym_alpha_ctx_left_is_sym ([])) ha)))) s}
        in
        case ehy of {
         ExistT x4 p0 ->
          case p0 of {
           (,) s0 a2 ->
            x1 x4 s0 y h0 a0
              (alpha_extend_ids ([]) x4 (h0 y) Id_ctx_nil
                (alpha_trans x4 x3 (h0 y) ([]) ([]) ([]) Alpha_trans_nil
                  (alpha_sym x3 x4 (sym_alpha_ctx ([])) ([])
                    (sym_alpha_ctx_left_is_sym ([])) a2) a1))}}}})) v b x h a
    halpha

sn_preimage__UU03b1_ :: (Term0 -> Term0) -> Term0 -> (Term0 -> Term0 ->
                        Step_gu -> SigT Term0 ((,) Step_gu Alpha)) -> (Sn
                        Term0 Step_gu) -> Sn Term0 Step_gu
sn_preimage__UU03b1_ h x x0 x1 =
  sn_preimage__UU03b1_' h x (h x) x0 x1
    (alpha_refl (h x) ([]) Alpha_refl_nil)

sn_ty_fun :: BSort -> Term0 -> Term0 -> (Sn Term0 Step_gu) -> (Sn Term0
             Step_gu) -> Sn Term0 Step_gu
sn_ty_fun b s t hSN_s hSN_t =
  sn_rect (\x _ x0 t0 _top_assumption_ ->
    let {
     _evar_0_ = \x1 s0 x2 -> SNI (\_ h ->
      case h of {
       Step_gu_intro _ _ _ x3 x4 x5 ->
        case x3 of {
         Alpha_app _ _ s2 _ t2 _ x6 x7 ->
          case x5 of {
           Step_appL0 _ _ s3 _ x8 ->
            let {
             h7 = step_naive_preserves_alpha2 s2 s3 (to_GU x) ([])
                    (gu_app_l b s2 t2 x4) (to_GU__GU x)
                    (alpha_extend_ids ([]) s2 (to_GU x) Id_ctx_nil
                      (alpha_extend_ids ([]) s2 (to_GU x) Id_ctx_nil
                        (alpha_trans s2 x (to_GU x) ([]) ([]) ([])
                          Alpha_trans_nil
                          (alpha_sym x s2 (sym_alpha_ctx ([])) ([])
                            (sym_alpha_ctx_left_is_sym ([])) x6)
                          (to_GU__alpha x)))) x8}
            in
            case h7 of {
             ExistT x9 p ->
              case p of {
               (,) s1 a ->
                _UU03b1__preserves_SN_R (Tmbin b x9 t2) (Tmbin b s3 t2) ([])
                  (alpha_extend_ids ([]) (Tmbin b x9 t2) (Tmbin b s3 t2)
                    Id_ctx_nil (Alpha_app b x9 s3 t2 t2 ([])
                    (alpha_sym s3 x9 (sym_alpha_ctx ([])) ([])
                      (sym_alpha_ctx_left_is_sym ([])) a)
                    (alpha_refl t2 ([]) Alpha_refl_nil)))
                  (x0 x9 (Step_gu_intro x (to_GU x) x9 (to_GU__alpha x)
                    (to_GU__GU x) s1) t2
                    (_UU03b1__preserves_SN_R x1 t2 ([]) x7 (SNI s0)))}};
           Step_appR0 _ _ _ t3 x8 ->
            let {
             h7 = step_naive_preserves_alpha2 t2 t3 (to_GU x1) ([])
                    (gu_app_r b s2 t2 x4) (to_GU__GU x1)
                    (alpha_extend_ids ([]) t2 (to_GU x1) Id_ctx_nil
                      (alpha_extend_ids ([]) t2 (to_GU x1) Id_ctx_nil
                        (alpha_trans t2 x1 (to_GU x1) ([]) ([]) ([])
                          Alpha_trans_nil
                          (alpha_sym x1 t2 (sym_alpha_ctx ([])) ([])
                            (sym_alpha_ctx_left_is_sym ([])) x7)
                          (to_GU__alpha x1)))) x8}
            in
            case h7 of {
             ExistT x9 p ->
              case p of {
               (,) s1 a ->
                _UU03b1__preserves_SN_R (Tmbin b x x9) (Tmbin b s2 t3) ([])
                  (alpha_extend_ids ([]) (Tmbin b x x9) (Tmbin b s2 t3)
                    Id_ctx_nil
                    (alpha_extend_ids ([]) (Tmbin b x x9) (Tmbin b s2 t3)
                      Id_ctx_nil (Alpha_app b x s2 x9 t3 ([]) x6
                      (alpha_sym t3 x9 (sym_alpha_ctx ([])) ([])
                        (sym_alpha_ctx_left_is_sym ([])) a))))
                  (x2 x9 (Step_gu_intro x1 (to_GU x1) x9 (to_GU__alpha x1)
                    (to_GU__GU x1) s1))}};
           _ -> Prelude.error "absurd case"};
         _ -> Prelude.error "absurd case"}})}
    in
    sn_rect _evar_0_ t0 _top_assumption_) s hSN_s t hSN_t

sn_ty_forall :: USort -> Prelude.String -> Kind -> Term0 -> (Sn Term0
                Step_gu) -> Sn Term0 Step_gu
sn_ty_forall b x k t x0 =
  sn_rect (\x1 _ x2 -> SNI (\_ hstep ->
    case hstep of {
     Step_gu_intro _ _ _ x3 x4 x5 ->
      case x3 of {
       Alpha_lam _ _ y _ _ s2 _ x6 ->
        case x5 of {
         Step_abs0 _ _ _ _ s3 x7 ->
          let {
           h7 = step_naive_preserves_alpha2 s2 s3 (to_GU x1) ((:) ((,) y x)
                  ([])) (gu_lam b y k s2 x4) (to_GU__GU x1)
                  (alpha_trans s2 x1 (to_GU x1) ((:) ((,) y x) ([])) ((:)
                    ((,) x x) ([])) ((:) ((,) y x) ([])) (Alpha_trans_cons y
                    x x ([]) ([]) ([]) Alpha_trans_nil)
                    (alpha_sym x1 s2 (sym_alpha_ctx ((:) ((,) y x) ([])))
                      ((:) ((,) y x) ([]))
                      (sym_alpha_ctx_left_is_sym ((:) ((,) y x) ([]))) x6)
                    (alpha_extend_ids ((:) ((,) x x) ([])) x1 (to_GU x1)
                      (Id_ctx_cons x ([]) Id_ctx_nil) (to_GU__alpha x1))) x7}
          in
          case h7 of {
           ExistT x8 p ->
            case p of {
             (,) s a ->
              _UU03b1__preserves_SN_R (Tmabs b x k x8) (Tmabs b y k s3) ([])
                (Alpha_lam b x y k x8 s3 ([])
                (alpha_sym s3 x8 (sym_alpha_ctx ((:) ((,) x y) ([]))) ((:)
                  ((,) x y) ([]))
                  (sym_alpha_ctx_left_is_sym ((:) ((,) x y) ([]))) a))
                (x2 x8 (Step_gu_intro x1 (to_GU x1) x8 (to_GU__alpha x1)
                  (to_GU__GU x1) s))}};
         _ -> Prelude.error "absurd case"};
       _ -> Prelude.error "absurd case"}})) t x0

sn_closedL :: BSort -> Term0 -> Term0 -> (Sn Term0 Step_gu) -> Sn Term0
              Step_gu
sn_closedL b t s =
  sn_preimage__UU03b1_ (\x -> Tmbin b x t) s (\x y h ->
    let {h0 = step_gu_app_l b x t y h} in
    case h0 of {
     ExistT x0 p ->
      case p of {
       (,) a s0 ->
        case s0 of {
         ExistT x1 p0 ->
          case p0 of {
           (,) a0 s1 -> ExistT (Tmbin b x0 x1) ((,) s1
            (alpha_sym (Tmbin b y t) (Tmbin b x0 x1) (sym_alpha_ctx ([]))
              ([]) (sym_alpha_ctx_left_is_sym ([])) (Alpha_app b y x0 t x1
              (sym_alpha_ctx ([])) a a0)))}}}})

step_subst_single :: (([]) ((,) Prelude.String Prelude.String)) ->
                     Prelude.String -> Term0 -> Term0 -> Term0 -> Term0 ->
                     Step_naive -> GU -> NC -> Alpha -> Coq__UU03b1_CtxSub ->
                     NC -> SigT Term0 ((,) Step_gu Alpha)
step_subst_single r x p s t t' x0 x1 x2 x3 x4 x5 =
  step_naive_rec (\x6 a s0 t0 h0 h1 r0 h3 t'0 h2 h4 ->
    let {
     h = to_GU_applam_unfold App Lam a (psubs ((:) ((,) x p) ([])) s0)
           (psubs ((:) ((,) x p) ([])) t0)
           (to_GU (Tmbin App (Tmabs Lam x6 a (psubs ((:) ((,) x p) ([])) s0))
             (psubs ((:) ((,) x p) ([])) t0))) x6}
    in
    case h of {
     ExistT x7 s1 ->
      case s1 of {
       ExistT x8 s2 ->
        case s2 of {
         ExistT x9 p0 ->
          case p0 of {
           (,) p1 a0 ->
            case p1 of {
             (,) _ a1 -> ExistT (sub x7 x9 x8) ((,) (Step_gu_intro
              (psubs ((:) ((,) x p) ([])) (Tmbin App (Tmabs Lam x6 a s0) t0))
              (Tmbin App (Tmabs Lam x7 a x8) x9) (sub x7 x9 x8) (Alpha_app
              App (Tmabs Lam x6 a
              (let {
                psubs0 sigma t1 =
                  case t1 of {
                   Tmvar x10 ->
                    case lookup x10 sigma of {
                     Prelude.Just t2 -> t2;
                     Prelude.Nothing -> Tmvar x10};
                   Tmabs b x10 a2 s3 -> Tmabs b x10 a2 (psubs0 sigma s3);
                   Tmbin b s3 t2 -> Tmbin b (psubs0 sigma s3)
                    (psubs0 sigma t2);
                   Tmbuiltin d -> Tmbuiltin d}}
               in psubs0 ((:) ((,) x p) ([])) s0)) (Tmabs Lam x7 a x8)
              (let {
                psubs0 sigma t1 =
                  case t1 of {
                   Tmvar x10 ->
                    case lookup x10 sigma of {
                     Prelude.Just t2 -> t2;
                     Prelude.Nothing -> Tmvar x10};
                   Tmabs b x10 a2 s3 -> Tmabs b x10 a2 (psubs0 sigma s3);
                   Tmbin b s3 t2 -> Tmbin b (psubs0 sigma s3)
                    (psubs0 sigma t2);
                   Tmbuiltin d -> Tmbuiltin d}}
               in psubs0 ((:) ((,) x p) ([])) t0) x9 ([]) (Alpha_lam Lam x6
              x7 a
              (let {
                psubs0 sigma t1 =
                  case t1 of {
                   Tmvar x10 ->
                    case lookup x10 sigma of {
                     Prelude.Just t2 -> t2;
                     Prelude.Nothing -> Tmvar x10};
                   Tmabs b x10 a2 s3 -> Tmabs b x10 a2 (psubs0 sigma s3);
                   Tmbin b s3 t2 -> Tmbin b (psubs0 sigma s3)
                    (psubs0 sigma t2);
                   Tmbuiltin d -> Tmbuiltin d}}
               in psubs0 ((:) ((,) x p) ([])) s0) x8 ([]) a1) a0)
              (to_GU__GU (Tmbin App (Tmabs Lam x6 a
                (psubs ((:) ((,) x p) ([])) s0))
                (psubs ((:) ((,) x p) ([])) t0))) (Step_beta0 x7 a x8 x9))
              (let {sconstr2_ = sconstr2 x6 t0 x p s0} in
               case sconstr2_ of {
                (,) p2 t1 ->
                 case p2 of {
                  (,) t2 t3 ->
                   alpha_trans (sub x7 x9 x8)
                     (sub x6 (psubs ((:) ((,) x t1) ([])) t3)
                       (psubs ((:) ((,) x t1) ([])) t2))
                     (psubs ((:) ((,) x p) ([])) t'0) (ctx_id_left r0) r0 r0
                     (id_left_trans r0)
                     (alpha_extend_ids (ctx_id_left r0) (sub x7 x9 x8)
                       (sub x6 (psubs ((:) ((,) x t1) ([])) t3)
                         (psubs ((:) ((,) x t1) ([])) t2))
                       (ctx_id_left_is_id r0)
                       (alpha_rename_binder_stronger x7 x6 x8 x9
                         (psubs ((:) ((,) x t1) ([])) t3) ([])
                         (psubs ((:) ((,) x t1) ([])) t2) ((:) ((,) x7 x6)
                         ([]))
                         (alpha_trans x8 (psubs ((:) ((,) x p) ([])) s0)
                           (psubs ((:) ((,) x t1) ([])) t2) ((:) ((,) x7 x6)
                           ([])) ((:) ((,) x6 x6) ([])) ((:) ((,) x7 x6)
                           ([])) (Alpha_trans_cons x7 x6 x6 ([]) ([]) ([])
                           Alpha_trans_nil)
                           (alpha_sym (psubs ((:) ((,) x p) ([])) s0) x8
                             (sym_alpha_ctx ((:) ((,) x7 x6) ([]))) ((:) ((,)
                             x7 x6) ([]))
                             (sym_alpha_ctx_left_is_sym ((:) ((,) x7 x6)
                               ([]))) a1)
                           (alpha_extend_ids ((:) ((,) x6 x6) ([]))
                             (psubs ((:) ((,) x p) ([])) s0)
                             (psubs ((:) ((,) x t1) ([])) t2) (Id_ctx_cons x6
                             ([]) Id_ctx_nil)
                             (psubs___UU03b1_ s0 ([]) t2 ((:) ((,) x p) ([]))
                               ((:) ((,) x t1) ([]))
                               (nc_lam Lam x6 s0 a ((:) ((,) x p) ([]))
                                 (nc_app_l App (Tmabs Lam x6 a s0) t0 ((:)
                                   ((,) x p) ([])) h1))
                               (sconstr2_nc_s x6 t0 x p s0 t2 t3 t1)
                               (alpha_extend_ids ([]) s0 t2 Id_ctx_nil
                                 (alpha_extend_ids ([]) s0 t2 Id_ctx_nil
                                   (alpha_extend_ids ([]) s0 t2 Id_ctx_nil
                                     (sconstr2_alpha_s x6 t0 x p s0 t2 t3 t1))))
                               (Alpha_ctx_cons ([]) ([]) ([]) x x p t1
                               (Alpha_ctx_nil ([])) (Alpha_var_refl x)
                               (alpha_extend_ids ([]) p t1 Id_ctx_nil
                                 (alpha_extend_ids ([]) p t1 Id_ctx_nil
                                   (sconstr2_alpha_p x6 t0 x p s0 t2 t3 t1)))))))
                         (alpha_trans x9 (psubs ((:) ((,) x p) ([])) t0)
                           (psubs ((:) ((,) x t1) ([])) t3) ([]) ([]) ([])
                           Alpha_trans_nil
                           (alpha_extend_ids ([]) x9
                             (psubs ((:) ((,) x p) ([])) t0) Id_ctx_nil
                             (alpha_extend_ids ([]) x9
                               (psubs ((:) ((,) x p) ([])) t0) Id_ctx_nil
                               (alpha_extend_ids ([]) x9
                                 (psubs ((:) ((,) x p) ([])) t0) Id_ctx_nil
                                 (alpha_sym (psubs ((:) ((,) x p) ([])) t0)
                                   x9 (sym_alpha_ctx ([])) ([])
                                   (sym_alpha_ctx_left_is_sym ([])) a0))))
                           (psubs___UU03b1_ t0 ([]) t3 ((:) ((,) x p) ([]))
                             ((:) ((,) x t1) ([]))
                             (nc_app_r App (Tmabs Lam x6 a s0) t0 ((:) ((,) x
                               p) ([])) h1)
                             (sconstr2_nc_t x6 t0 x p s0 t2 t3 t1)
                             (alpha_extend_ids ([]) t0 t3 Id_ctx_nil
                               (alpha_extend_ids ([]) t0 t3 Id_ctx_nil
                                 (alpha_extend_ids ([]) t0 t3 Id_ctx_nil
                                   (sconstr2_alpha_t x6 t0 x p s0 t2 t3 t1))))
                             (Alpha_ctx_cons ([]) ([]) ([]) x x p t1
                             (Alpha_ctx_nil ([])) (Alpha_var_refl x)
                             (alpha_extend_ids ([]) p t1 Id_ctx_nil
                               (alpha_extend_ids ([]) p t1 Id_ctx_nil
                                 (sconstr2_alpha_p x6 t0 x p s0 t2 t3 t1))))))
                         StarR
                         (gu_applam_to_nc App Lam x8 x9 x7 a
                           (to_GU__GU (Tmbin App (Tmabs Lam x6 a
                             (psubs ((:) ((,) x p) ([])) s0))
                             (psubs ((:) ((,) x p) ([])) t0))))
                         (sconstr2_nc_sub x6 t0 x p s0 t2 t3 t1)))
                     (commute_sub_naive r0 x6 t2 t3 ((:) ((,) x t1) ([]))
                       ((:) ((,) x p) ([])) t'0
                       (alpha_trans (sub x6 t3 t2) (sub x6 t0 s0) t'0
                         (ctx_id_left r0) r0 r0 (id_left_trans r0)
                         (alpha_extend_ids (ctx_id_left r0) (sub x6 t3 t2)
                           (sub x6 t0 s0) (ctx_id_left_is_id r0)
                           (psubs___UU03b1_ t2 ([]) s0 ((:) ((,) x6 t3) ([]))
                             ((:) ((,) x6 t0) ([]))
                             (sconstr2_nc_s_t x6 t0 x p s0 t2 t3 t1)
                             (gu_applam_to_nc App Lam s0 t0 x6 a h0)
                             (alpha_extend_ids ([]) t2 s0 Id_ctx_nil
                               (alpha_extend_ids ([]) t2 s0 Id_ctx_nil
                                 (alpha_sym s0 t2 (sym_alpha_ctx ([])) ([])
                                   (sym_alpha_ctx_left_is_sym ([]))
                                   (sconstr2_alpha_s x6 t0 x p s0 t2 t3 t1))))
                             (Alpha_ctx_cons ([]) ([]) ([]) x6 x6 t3 t0
                             (Alpha_ctx_nil ([])) (Alpha_var_refl x6)
                             (alpha_extend_ids ([]) t3 t0 Id_ctx_nil
                               (alpha_sym t0 t3 (sym_alpha_ctx ([])) ([])
                                 (sym_alpha_ctx_left_is_sym ([]))
                                 (sconstr2_alpha_t x6 t0 x p s0 t2 t3 t1))))))
                         h2)
                       (_UU03b1_ctx_trans (ctx_id_left r0) r0 r0 ((:) ((,) x
                         t1) ([])) ((:) ((,) x p) ([])) ((:) ((,) x p) ([]))
                         (id_left_trans r0) (Alpha_ctx_cons (ctx_id_left r0)
                         ([]) ([]) x x t1 p (Alpha_ctx_nil (ctx_id_left r0))
                         (alphavar_extend_ids (ctx_id_left r0) x x
                           (ctx_id_left_is_id r0) (Alpha_var_refl x))
                         (alpha_extend_ids (ctx_id_left r0) t1 p
                           (ctx_id_left_is_id r0)
                           (alpha_extend_ids ([]) t1 p Id_ctx_nil
                             (alpha_extend_ids ([]) t1 p Id_ctx_nil
                               (alpha_sym p t1 (sym_alpha_ctx ([])) ([])
                                 (sym_alpha_ctx_left_is_sym ([]))
                                 (sconstr2_alpha_p x6 t0 x p s0 t2 t3 t1))))))
                         h3) h4 (sconstr2_nc_s_t x6 t0 x p s0 t2 t3 t1)
                       (sconstr2_nc_s x6 t0 x p s0 t2 t3 t1)
                       (sconstr2_nc_t x6 t0 x p s0 t2 t3 t1)
                       (sconstr2_nc_sub x6 t0 x p s0 t2 t3 t1))}}))}}}}})
    (\b s1 s2 t0 _ iHHstep h0 h1 r0 h3 _ h2 h4 ->
    case h2 of {
     Alpha_var _ _ sigma x6 -> eq_rec_r r0 (\_ -> false_rec) sigma __ __ x6;
     Alpha_lam _ _ _ _ _ _ sigma x6 ->
      eq_rec_r r0 (\_ -> false_rec) sigma __ __ x6;
     Alpha_app b0 s3 s4 t1 t2 sigma x6 x7 ->
      eq_rec_r r0 (\_ ->
        eq_rec_r b (\_ ->
          eq_rec_r s2 (\_ ->
            eq_rec_r t0 (\_ h9 h10 ->
              let {
               s0 = iHHstep (gu_app_l b s1 t0 h0)
                      (nc_app_l b s1 t0 ((:) ((,) x p) ([])) h1) r0 h3 s4 h9
                      (nc_app_l b s4 t2 ((:) ((,) x p) ([])) h4)}
              in
              case s0 of {
               ExistT x8 p0 ->
                case p0 of {
                 (,) s5 a ->
                  case s5 of {
                   Step_gu_intro s6 s' t3 x9 x10 x11 ->
                    eq_rec_r (psubs ((:) ((,) x p) ([])) s1) (\_ ->
                      eq_rec_r x8 (\h h5 h6 ->
                        let {
                         st_gu = to_GU (Tmbin b s'
                                   (psubs ((:) ((,) x p) ([])) t0))}
                        in
                        let {
                         s7 = to_GU_app_unfold b s'
                                (psubs ((:) ((,) x p) ([])) t0) st_gu}
                        in
                        case s7 of {
                         ExistT x12 s8 ->
                          case s8 of {
                           ExistT x13 p1 ->
                            case p1 of {
                             (,) p2 a0 ->
                              case p2 of {
                               (,) _ a1 ->
                                eq_rec_r
                                  (to_GU (Tmbin b s'
                                    (psubs ((:) ((,) x p) ([])) t0))) (\_ ->
                                  let {
                                   h7 = step_naive_preserves_alpha2 s' x8 x12
                                          ([]) h5
                                          (gu_app_l b x12 x13
                                            (to_GU__GU (Tmbin b s'
                                              (psubs ((:) ((,) x p) ([])) t0))))
                                          a1 h6}
                                  in
                                  case h7 of {
                                   ExistT x14 p3 ->
                                    case p3 of {
                                     (,) s9 a2 -> ExistT (Tmbin b x14 x13)
                                      ((,) (Step_gu_intro
                                      (psubs ((:) ((,) x p) ([])) (Tmbin b s1
                                        t0)) (Tmbin b x12 x13) (Tmbin b x14
                                      x13)
                                      (alpha_extend_ids ([])
                                        (psubs ((:) ((,) x p) ([])) (Tmbin b
                                          s1 t0)) (Tmbin b x12 x13)
                                        Id_ctx_nil
                                        (alpha_extend_ids ([])
                                          (psubs ((:) ((,) x p) ([])) (Tmbin
                                            b s1 t0)) (Tmbin b x12 x13)
                                          Id_ctx_nil (Alpha_app b
                                          (let {
                                            psubs0 sigma0 t4 =
                                              case t4 of {
                                               Tmvar x15 ->
                                                case lookup x15 sigma0 of {
                                                 Prelude.Just t5 -> t5;
                                                 Prelude.Nothing -> Tmvar x15};
                                               Tmabs b1 x15 a3 s10 -> Tmabs
                                                b1 x15 a3 (psubs0 sigma0 s10);
                                               Tmbin b1 s10 t5 -> Tmbin b1
                                                (psubs0 sigma0 s10)
                                                (psubs0 sigma0 t5);
                                               Tmbuiltin d -> Tmbuiltin d}}
                                           in psubs0 ((:) ((,) x p) ([])) s1)
                                          x12
                                          (let {
                                            psubs0 sigma0 t4 =
                                              case t4 of {
                                               Tmvar x15 ->
                                                case lookup x15 sigma0 of {
                                                 Prelude.Just t5 -> t5;
                                                 Prelude.Nothing -> Tmvar x15};
                                               Tmabs b1 x15 a3 s10 -> Tmabs
                                                b1 x15 a3 (psubs0 sigma0 s10);
                                               Tmbin b1 s10 t5 -> Tmbin b1
                                                (psubs0 sigma0 s10)
                                                (psubs0 sigma0 t5);
                                               Tmbuiltin d -> Tmbuiltin d}}
                                           in psubs0 ((:) ((,) x p) ([])) t0)
                                          x13 ([])
                                          (alpha_trans
                                            (let {
                                              psubs0 sigma0 t4 =
                                                case t4 of {
                                                 Tmvar x15 ->
                                                  case lookup x15 sigma0 of {
                                                   Prelude.Just t5 -> t5;
                                                   Prelude.Nothing -> Tmvar
                                                    x15};
                                                 Tmabs b1 x15 a3 s10 -> Tmabs
                                                  b1 x15 a3
                                                  (psubs0 sigma0 s10);
                                                 Tmbin b1 s10 t5 -> Tmbin b1
                                                  (psubs0 sigma0 s10)
                                                  (psubs0 sigma0 t5);
                                                 Tmbuiltin d -> Tmbuiltin d}}
                                             in psubs0 ((:) ((,) x p) ([]))
                                                  s1) s' x12 ([]) ([]) ([])
                                            Alpha_trans_nil h a1) a0)))
                                      (to_GU__GU (Tmbin b s'
                                        (psubs ((:) ((,) x p) ([])) t0)))
                                      (Step_appL0 b x12 x14 x13 s9))
                                      (alpha_trans (Tmbin b x14 x13) (Tmbin b
                                        x8 (psubs ((:) ((,) x p) ([])) t0))
                                        (psubs ((:) ((,) x p) ([])) (Tmbin b
                                          s4 t2)) (ctx_id_left r0) r0 r0
                                        (id_left_trans r0)
                                        (alpha_extend_ids (ctx_id_left r0)
                                          (Tmbin b x14 x13) (Tmbin b x8
                                          (psubs ((:) ((,) x p) ([])) t0))
                                          (ctx_id_left_is_id r0) (Alpha_app b
                                          x14 x8 x13
                                          (psubs ((:) ((,) x p) ([])) t0)
                                          ([])
                                          (alpha_sym x8 x14 ([]) ([])
                                            Alpha_sym_nil a2)
                                          (alpha_sym
                                            (psubs ((:) ((,) x p) ([])) t0)
                                            x13 ([]) ([]) Alpha_sym_nil a0)))
                                        (Alpha_app b x8
                                        (let {
                                          psubs0 sigma0 t4 =
                                            case t4 of {
                                             Tmvar x15 ->
                                              case lookup x15 sigma0 of {
                                               Prelude.Just t5 -> t5;
                                               Prelude.Nothing -> Tmvar x15};
                                             Tmabs b1 x15 a3 s10 -> Tmabs b1
                                              x15 a3 (psubs0 sigma0 s10);
                                             Tmbin b1 s10 t5 -> Tmbin b1
                                              (psubs0 sigma0 s10)
                                              (psubs0 sigma0 t5);
                                             Tmbuiltin d -> Tmbuiltin d}}
                                         in psubs0 ((:) ((,) x p) ([])) s4)
                                        (psubs ((:) ((,) x p) ([])) t0)
                                        (let {
                                          psubs0 sigma0 t4 =
                                            case t4 of {
                                             Tmvar x15 ->
                                              case lookup x15 sigma0 of {
                                               Prelude.Just t5 -> t5;
                                               Prelude.Nothing -> Tmvar x15};
                                             Tmabs b1 x15 a3 s10 -> Tmabs b1
                                              x15 a3 (psubs0 sigma0 s10);
                                             Tmbin b1 s10 t5 -> Tmbin b1
                                              (psubs0 sigma0 s10)
                                              (psubs0 sigma0 t5);
                                             Tmbuiltin d -> Tmbuiltin d}}
                                         in psubs0 ((:) ((,) x p) ([])) t2)
                                        r0 a
                                        (psubs___UU03b1_ t0 r0 t2 ((:) ((,) x
                                          p) ([])) ((:) ((,) x p) ([]))
                                          (nc_app_r b s1 t0 ((:) ((,) x p)
                                            ([])) h1)
                                          (nc_app_r b s4 t2 ((:) ((,) x p)
                                            ([])) h4) h10 h3))))}}) st_gu __}}}})
                        t3) s6 __ x9 x10 x11}}}) t1) s3) b0 __ __) sigma __
        __ x6 x7;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ -> false_rec) r1 __ __})
    (\b s0 t1 t2 _ iHHstep h0 h1 r0 h3 _ h2 h4 ->
    case h2 of {
     Alpha_var _ _ sigma x6 -> eq_rec_r r0 (\_ -> false_rec) sigma __ __ x6;
     Alpha_lam _ _ _ _ _ _ sigma x6 ->
      eq_rec_r r0 (\_ -> false_rec) sigma __ __ x6;
     Alpha_app b0 s1 s2 t3 t4 sigma x6 x7 ->
      eq_rec_r r0 (\_ ->
        eq_rec_r b (\_ ->
          eq_rec_r s0 (\_ ->
            eq_rec_r t2 (\_ h9 h10 ->
              let {
               s3 = iHHstep (gu_app_r b s0 t1 h0)
                      (nc_app_r b s0 t1 ((:) ((,) x p) ([])) h1) r0 h3 t4 h10
                      (nc_app_r b s2 t4 ((:) ((,) x p) ([])) h4)}
              in
              case s3 of {
               ExistT x8 p0 ->
                case p0 of {
                 (,) s4 a ->
                  case s4 of {
                   Step_gu_intro s5 s' t0 x9 x10 x11 ->
                    eq_rec_r (psubs ((:) ((,) x p) ([])) t1) (\_ ->
                      eq_rec_r x8 (\h h5 h6 ->
                        let {
                         st_gu = to_GU (Tmbin b s'
                                   (psubs ((:) ((,) x p) ([])) s0))}
                        in
                        let {
                         s6 = to_GU_app_unfold b s'
                                (psubs ((:) ((,) x p) ([])) s0) st_gu}
                        in
                        case s6 of {
                         ExistT x12 s7 ->
                          case s7 of {
                           ExistT x13 p1 ->
                            case p1 of {
                             (,) p2 a0 ->
                              case p2 of {
                               (,) _ a1 ->
                                eq_rec_r
                                  (to_GU (Tmbin b s'
                                    (psubs ((:) ((,) x p) ([])) s0))) (\_ ->
                                  let {
                                   h7 = step_naive_preserves_alpha2 s' x8 x12
                                          ([]) h5
                                          (gu_app_l b x12 x13
                                            (to_GU__GU (Tmbin b s'
                                              (psubs ((:) ((,) x p) ([])) s0))))
                                          a1 h6}
                                  in
                                  case h7 of {
                                   ExistT x14 p3 ->
                                    case p3 of {
                                     (,) s8 a2 -> ExistT (Tmbin b x13 x14)
                                      ((,) (Step_gu_intro
                                      (psubs ((:) ((,) x p) ([])) (Tmbin b s0
                                        t1)) (Tmbin b x13 x12) (Tmbin b x13
                                      x14)
                                      (alpha_extend_ids ([])
                                        (psubs ((:) ((,) x p) ([])) (Tmbin b
                                          s0 t1)) (Tmbin b x13 x12)
                                        Id_ctx_nil
                                        (alpha_extend_ids ([])
                                          (psubs ((:) ((,) x p) ([])) (Tmbin
                                            b s0 t1)) (Tmbin b x13 x12)
                                          Id_ctx_nil (Alpha_app b
                                          (let {
                                            psubs0 sigma0 t5 =
                                              case t5 of {
                                               Tmvar x15 ->
                                                case lookup x15 sigma0 of {
                                                 Prelude.Just t6 -> t6;
                                                 Prelude.Nothing -> Tmvar x15};
                                               Tmabs b1 x15 a3 s9 -> Tmabs b1
                                                x15 a3 (psubs0 sigma0 s9);
                                               Tmbin b1 s9 t6 -> Tmbin b1
                                                (psubs0 sigma0 s9)
                                                (psubs0 sigma0 t6);
                                               Tmbuiltin d -> Tmbuiltin d}}
                                           in psubs0 ((:) ((,) x p) ([])) s0)
                                          x13
                                          (let {
                                            psubs0 sigma0 t5 =
                                              case t5 of {
                                               Tmvar x15 ->
                                                case lookup x15 sigma0 of {
                                                 Prelude.Just t6 -> t6;
                                                 Prelude.Nothing -> Tmvar x15};
                                               Tmabs b1 x15 a3 s9 -> Tmabs b1
                                                x15 a3 (psubs0 sigma0 s9);
                                               Tmbin b1 s9 t6 -> Tmbin b1
                                                (psubs0 sigma0 s9)
                                                (psubs0 sigma0 t6);
                                               Tmbuiltin d -> Tmbuiltin d}}
                                           in psubs0 ((:) ((,) x p) ([])) t1)
                                          x12 ([]) a0
                                          (alpha_trans
                                            (let {
                                              psubs0 sigma0 t5 =
                                                case t5 of {
                                                 Tmvar x15 ->
                                                  case lookup x15 sigma0 of {
                                                   Prelude.Just t6 -> t6;
                                                   Prelude.Nothing -> Tmvar
                                                    x15};
                                                 Tmabs b1 x15 a3 s9 -> Tmabs
                                                  b1 x15 a3
                                                  (psubs0 sigma0 s9);
                                                 Tmbin b1 s9 t6 -> Tmbin b1
                                                  (psubs0 sigma0 s9)
                                                  (psubs0 sigma0 t6);
                                                 Tmbuiltin d -> Tmbuiltin d}}
                                             in psubs0 ((:) ((,) x p) ([]))
                                                  t1) s' x12 ([]) ([]) ([])
                                            Alpha_trans_nil h a1))))
                                      (gu_app_st__gu_app_ts b x12 x13
                                        (to_GU__GU (Tmbin b s'
                                          (psubs ((:) ((,) x p) ([])) s0))))
                                      (Step_appR0 b x13 x12 x14 s8))
                                      (alpha_trans (Tmbin b x13 x14) (Tmbin b
                                        (psubs ((:) ((,) x p) ([])) s0) x8)
                                        (psubs ((:) ((,) x p) ([])) (Tmbin b
                                          s2 t4)) (ctx_id_left r0) r0 r0
                                        (id_left_trans r0)
                                        (alpha_extend_ids (ctx_id_left r0)
                                          (Tmbin b x13 x14) (Tmbin b
                                          (psubs ((:) ((,) x p) ([])) s0) x8)
                                          (ctx_id_left_is_id r0)
                                          (alpha_extend_ids ([]) (Tmbin b x13
                                            x14) (Tmbin b
                                            (psubs ((:) ((,) x p) ([])) s0)
                                            x8) Id_ctx_nil
                                            (alpha_extend_ids ([]) (Tmbin b
                                              x13 x14) (Tmbin b
                                              (psubs ((:) ((,) x p) ([])) s0)
                                              x8) Id_ctx_nil
                                              (alpha_sym (Tmbin b
                                                (psubs ((:) ((,) x p) ([]))
                                                  s0) x8) (Tmbin b x13 x14)
                                                (sym_alpha_ctx ([])) ([])
                                                (sym_alpha_ctx_left_is_sym
                                                  ([])) (Alpha_app b
                                                (psubs ((:) ((,) x p) ([]))
                                                  s0) x13 x8 x14
                                                (sym_alpha_ctx ([])) a0 a2)))))
                                        (Alpha_app b
                                        (psubs ((:) ((,) x p) ([])) s0)
                                        (let {
                                          psubs0 sigma0 t5 =
                                            case t5 of {
                                             Tmvar x15 ->
                                              case lookup x15 sigma0 of {
                                               Prelude.Just t6 -> t6;
                                               Prelude.Nothing -> Tmvar x15};
                                             Tmabs b1 x15 a3 s9 -> Tmabs b1
                                              x15 a3 (psubs0 sigma0 s9);
                                             Tmbin b1 s9 t6 -> Tmbin b1
                                              (psubs0 sigma0 s9)
                                              (psubs0 sigma0 t6);
                                             Tmbuiltin d -> Tmbuiltin d}}
                                         in psubs0 ((:) ((,) x p) ([])) s2)
                                        x8
                                        (let {
                                          psubs0 sigma0 t5 =
                                            case t5 of {
                                             Tmvar x15 ->
                                              case lookup x15 sigma0 of {
                                               Prelude.Just t6 -> t6;
                                               Prelude.Nothing -> Tmvar x15};
                                             Tmabs b1 x15 a3 s9 -> Tmabs b1
                                              x15 a3 (psubs0 sigma0 s9);
                                             Tmbin b1 s9 t6 -> Tmbin b1
                                              (psubs0 sigma0 s9)
                                              (psubs0 sigma0 t6);
                                             Tmbuiltin d -> Tmbuiltin d}}
                                         in psubs0 ((:) ((,) x p) ([])) t4)
                                        r0
                                        (psubs___UU03b1_ s0 r0 s2 ((:) ((,) x
                                          p) ([])) ((:) ((,) x p) ([]))
                                          (nc_app_l b s0 t1 ((:) ((,) x p)
                                            ([])) h1)
                                          (nc_app_l b s2 t4 ((:) ((,) x p)
                                            ([])) h4) h9 h3) a)))}}) st_gu __}}}})
                        t0) s5 __ x9 x10 x11}}}) t3) s1) b0 __ __) sigma __
        __ x6 x7;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ -> false_rec) r1 __ __})
    (\b x6 a s1 s2 _ iHHstep h0 h1 r0 h3 _ h2 h4 ->
    case h2 of {
     Alpha_var _ _ sigma x7 -> eq_rec_r r0 (\_ -> false_rec) sigma __ __ x7;
     Alpha_lam b0 x7 y a0 s3 s4 sigma x8 ->
      eq_rec_r r0 (\_ ->
        eq_rec_r b (\_ ->
          eq_rec_r x6 (\_ ->
            eq_rec_r a (\_ ->
              eq_rec_r s2 (\_ h10 ->
                let {
                 s0 = iHHstep (gu_lam b x6 a s1 h0)
                        (nc_lam b x6 s1 a ((:) ((,) x p) ([])) h1) ((:) ((,)
                        x6 y) r0)
                        (alpha_ctx_ren_extend_fresh_ftv ((:) ((,) x p) ([]))
                          ((:) ((,) x p) ([])) x6 y r0 h3) s4 h10
                        (nc_lam b y s4 a ((:) ((,) x p) ([])) h4)}
                in
                case s0 of {
                 ExistT x9 p0 ->
                  case p0 of {
                   (,) s5 a1 ->
                    case s5 of {
                     Step_gu_intro s6 s' t0 x10 x11 x12 ->
                      eq_rec_r (psubs ((:) ((,) x p) ([])) s1) (\_ ->
                        eq_rec_r x9 (\h h5 hstep_na ->
                          let {
                           hstep_na0 = step_naive_preserves_alpha2 s' x9
                                         (to_GU'' x6 s') ([]) h5
                                         (to_GU''__GU x6 s')
                                         (to_GU''__alpha x6 s') hstep_na}
                          in
                          case hstep_na0 of {
                           ExistT x13 p1 ->
                            case p1 of {
                             (,) s7 a2 -> ExistT (Tmabs b x6 a x13) ((,)
                              (Step_gu_intro
                              (psubs ((:) ((,) x p) ([])) (Tmabs b x6 a s1))
                              (Tmabs b x6 a (to_GU'' x6 s')) (Tmabs b x6 a
                              x13) (Alpha_lam b x6 x6 a
                              (let {
                                psubs0 sigma0 t1 =
                                  case t1 of {
                                   Tmvar x14 ->
                                    case lookup x14 sigma0 of {
                                     Prelude.Just t2 -> t2;
                                     Prelude.Nothing -> Tmvar x14};
                                   Tmabs b1 x14 a3 s8 -> Tmabs b1 x14 a3
                                    (psubs0 sigma0 s8);
                                   Tmbin b1 s8 t2 -> Tmbin b1
                                    (psubs0 sigma0 s8) (psubs0 sigma0 t2);
                                   Tmbuiltin d -> Tmbuiltin d}}
                               in psubs0 ((:) ((,) x p) ([])) s1)
                              (to_GU'' x6 s') ([])
                              (alpha_extend_ids ((:) ((,) x6 x6) ([]))
                                (let {
                                  psubs0 sigma0 t1 =
                                    case t1 of {
                                     Tmvar x14 ->
                                      case lookup x14 sigma0 of {
                                       Prelude.Just t2 -> t2;
                                       Prelude.Nothing -> Tmvar x14};
                                     Tmabs b1 x14 a3 s8 -> Tmabs b1 x14 a3
                                      (psubs0 sigma0 s8);
                                     Tmbin b1 s8 t2 -> Tmbin b1
                                      (psubs0 sigma0 s8) (psubs0 sigma0 t2);
                                     Tmbuiltin d -> Tmbuiltin d}}
                                 in psubs0 ((:) ((,) x p) ([])) s1)
                                (to_GU'' x6 s') (Id_ctx_cons x6 ([])
                                Id_ctx_nil)
                                (alpha_trans
                                  (let {
                                    psubs0 sigma0 t1 =
                                      case t1 of {
                                       Tmvar x14 ->
                                        case lookup x14 sigma0 of {
                                         Prelude.Just t2 -> t2;
                                         Prelude.Nothing -> Tmvar x14};
                                       Tmabs b1 x14 a3 s8 -> Tmabs b1 x14 a3
                                        (psubs0 sigma0 s8);
                                       Tmbin b1 s8 t2 -> Tmbin b1
                                        (psubs0 sigma0 s8) (psubs0 sigma0 t2);
                                       Tmbuiltin d -> Tmbuiltin d}}
                                   in psubs0 ((:) ((,) x p) ([])) s1) s'
                                  (to_GU'' x6 s') ([]) ([]) ([])
                                  Alpha_trans_nil h (to_GU''__alpha x6 s'))))
                              (to_GU''__GU_lam b x6 a s') (Step_abs0 b x6 a
                              (to_GU'' x6 s') x13 s7)) (Alpha_lam b x6 y a
                              x13
                              (let {
                                psubs0 sigma0 t1 =
                                  case t1 of {
                                   Tmvar x14 ->
                                    case lookup x14 sigma0 of {
                                     Prelude.Just t2 -> t2;
                                     Prelude.Nothing -> Tmvar x14};
                                   Tmabs b1 x14 a3 s8 -> Tmabs b1 x14 a3
                                    (psubs0 sigma0 s8);
                                   Tmbin b1 s8 t2 -> Tmbin b1
                                    (psubs0 sigma0 s8) (psubs0 sigma0 t2);
                                   Tmbuiltin d -> Tmbuiltin d}}
                               in psubs0 ((:) ((,) x p) ([])) s4) r0
                              (alpha_trans x13 x9
                                (let {
                                  psubs0 sigma0 t1 =
                                    case t1 of {
                                     Tmvar x14 ->
                                      case lookup x14 sigma0 of {
                                       Prelude.Just t2 -> t2;
                                       Prelude.Nothing -> Tmvar x14};
                                     Tmabs b1 x14 a3 s8 -> Tmabs b1 x14 a3
                                      (psubs0 sigma0 s8);
                                     Tmbin b1 s8 t2 -> Tmbin b1
                                      (psubs0 sigma0 s8) (psubs0 sigma0 t2);
                                     Tmbuiltin d -> Tmbuiltin d}}
                                 in psubs0 ((:) ((,) x p) ([])) s4)
                                (ctx_id_left ((:) ((,) x6 y) r0)) ((:) ((,)
                                x6 y) r0) ((:) ((,) x6 y) r0)
                                (id_left_trans ((:) ((,) x6 y) r0))
                                (alpha_extend_ids
                                  (ctx_id_left ((:) ((,) x6 y) r0)) x13 x9
                                  (ctx_id_left_is_id ((:) ((,) x6 y) r0))
                                  (alpha_extend_ids ([]) x13 x9 Id_ctx_nil
                                    (alpha_extend_ids ([]) x13 x9 Id_ctx_nil
                                      (alpha_extend_ids ([]) x13 x9
                                        Id_ctx_nil
                                        (alpha_sym x9 x13
                                          (sym_alpha_ctx ([])) ([])
                                          (sym_alpha_ctx_left_is_sym ([]))
                                          a2))))) a1)))}}) t0) s6 __ x10 x11
                        x12}}}) s3) a0) x7) b0 __ __ __) sigma __ __ x8;
     Alpha_app _ _ _ _ _ sigma x7 x8 ->
      eq_rec_r r0 (\_ -> false_rec) sigma __ __ x7 x8;
     Alpha_builtin r1 _ -> eq_rec_r r0 (\_ -> false_rec) r1 __ __}) s t x0 x1
    x2 r x4 t' x3 x5

sub_gu :: Prelude.String -> Term0 -> Term0 -> Term0
sub_gu x t s =
  sub x t (to_GU' x t s)

sn_subst :: Prelude.String -> Term0 -> Term0 -> NC -> (Sn Term0 Step_gu) ->
            Sn Term0 Step_gu
sn_subst x t s hnc hSN_sub =
  let {
   hSN_sub0 = _UU03b1__preserves_SN_R (psubs ((:) ((,) x t) ([])) s)
                (psubs ((:) ((,) x t) ([])) (to_GU' x t s)) ([])
                (psubs___UU03b1_ s ([]) (to_GU' x t s) ((:) ((,) x t) ([]))
                  ((:) ((,) x t) ([])) hnc (to_GU'__NC x t s)
                  (to_GU'__alpha x t s) (Alpha_ctx_cons ([]) ([]) ([]) x x t
                  t (Alpha_ctx_nil ([])) (Alpha_var_refl x)
                  (alpha_refl t ([]) Alpha_refl_nil))) hSN_sub}
  in
  sn_preimage__UU03b1_ (sub_gu x t) s (\x0 y hstep ->
    case hstep of {
     Step_gu_intro s0 s' t0 x1 x2 x3 ->
      eq_rec_r x0 (\_ ->
        eq_rec_r y (\h h0 h1 ->
          let {
           h2 = step_naive_preserves_alpha2 s' y (to_GU' x t x0) ([]) h0
                  (to_GU'__GU x t x0)
                  (alpha_trans s' x0 (to_GU' x t x0) ([]) ([]) ([])
                    Alpha_trans_nil
                    (alpha_extend_ids ([]) s' x0 Id_ctx_nil
                      (alpha_extend_ids ([]) s' x0 Id_ctx_nil
                        (alpha_extend_ids ([]) s' x0 Id_ctx_nil
                          (alpha_sym x0 s' (sym_alpha_ctx ([])) ([])
                            (sym_alpha_ctx_left_is_sym ([])) h))))
                    (to_GU'__alpha x t x0)) h1}
          in
          case h2 of {
           ExistT x4 p ->
            case p of {
             (,) s1 a ->
              step_subst_single ([]) x t (to_GU' x t x0) x4 (to_GU' x t y) s1
                (to_GU'__GU x t x0) (to_GU'__NC x t x0)
                (alpha_trans x4 y (to_GU' x t y) ([]) ([]) ([])
                  Alpha_trans_nil
                  (alpha_extend_ids ([]) x4 y Id_ctx_nil
                    (alpha_extend_ids ([]) x4 y Id_ctx_nil
                      (alpha_extend_ids ([]) x4 y Id_ctx_nil
                        (alpha_sym y x4 (sym_alpha_ctx ([])) ([])
                          (sym_alpha_ctx_left_is_sym ([])) a))))
                  (to_GU'__alpha x t y)) (Alpha_ctx_cons ([]) ([]) ([]) x x t
                t (Alpha_ctx_nil ([])) (Alpha_var_refl x)
                (alpha_refl t ([]) Alpha_refl_nil)) (to_GU'__NC x t y)}}) t0)
        s0 __ x1 x2 x3}) hSN_sub0

red_beta :: Prelude.String -> Term0 -> Term0 -> Term0 -> Step_gu -> NC ->
            SigT Term0 ((,) Red_gu_na Alpha)
red_beta x s t1 t2 hstep hNC_t1 =
  term_rec (\s0 hNC_t2 -> ExistT (sub x t2 (Tmvar s0)) ((,)
    (let {
      b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
            x s0}
     in
     case b of {
      Prelude.True ->
       eq_rec_r s0 (\_ ->
         let {_evar_0_ = Red_gu_na_star t1 t2 t2 hstep (Red_gu_na_nil t2)} in
         eq_rec_r Prelude.True _evar_0_
           (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             s0 s0)) x hNC_t2;
      Prelude.False ->
       let {_evar_0_ = Red_gu_na_nil (Tmvar s0)} in
       eq_rec_r Prelude.False _evar_0_
         (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           x s0)}) (alpha_refl (sub x t2 (Tmvar s0)) ([]) Alpha_refl_nil)))
    (\uSort s0 k s1 iHs hNC_t2 ->
    let {h = iHs (nc_lam uSort s0 s1 k ((:) ((,) x t1) ([])) hNC_t2)} in
    case h of {
     ExistT x0 p ->
      case p of {
       (,) r a ->
        let {h0 = red_gu_na_lam_fold uSort s0 k (sub x t1 s1) x0 r} in
        case h0 of {
         ExistT x1 p0 ->
          case p0 of {
           (,) r0 a0 -> ExistT x1 ((,) r0
            (alpha_trans x1 (Tmabs uSort s0 k x0)
              (sub x t2 (Tmabs uSort s0 k s1)) ([]) ([]) ([]) Alpha_trans_nil
              a0 (Alpha_lam uSort s0 s0 k x0
              (let {
                sub0 x2 u t =
                  case t of {
                   Tmvar y ->
                    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                           x2 y of {
                     Prelude.True -> u;
                     Prelude.False -> Tmvar y};
                   Tmabs b y k1 t' -> Tmabs b y k1 (sub0 x2 u t');
                   Tmbin b t3 t4 -> Tmbin b (sub0 x2 u t3) (sub0 x2 u t4);
                   Tmbuiltin d -> Tmbuiltin d}}
               in sub0 x t2 s1) ([])
              (alpha_extend_ids ((:) ((,) s0 s0) ([])) x0
                (let {
                  sub0 x2 u t =
                    case t of {
                     Tmvar y ->
                      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                             x2 y of {
                       Prelude.True -> u;
                       Prelude.False -> Tmvar y};
                     Tmabs b y k1 t' -> Tmabs b y k1 (sub0 x2 u t');
                     Tmbin b t3 t4 -> Tmbin b (sub0 x2 u t3) (sub0 x2 u t4);
                     Tmbuiltin d -> Tmbuiltin d}}
                 in sub0 x t2 s1) (Id_ctx_cons s0 ([]) Id_ctx_nil) a))))}}}})
    (\bSort s1 iHs1 s2 iHs2 hNC_t2 ->
    let {h = iHs1 (nc_app_l bSort s1 s2 ((:) ((,) x t1) ([])) hNC_t2)} in
    case h of {
     ExistT x0 p ->
      case p of {
       (,) r a ->
        let {h0 = iHs2 (nc_app_r bSort s1 s2 ((:) ((,) x t1) ([])) hNC_t2)}
        in
        case h0 of {
         ExistT x1 p0 ->
          case p0 of {
           (,) r0 a0 ->
            let {
             h1 = red_gu_na_app_fold bSort (sub x t1 s1) x0 (sub x t1 s2) x1
                    r r0}
            in
            case h1 of {
             ExistT x2 p1 ->
              case p1 of {
               (,) r1 a1 -> ExistT x2 ((,) r1
                (alpha_extend_ids ([]) x2 (sub x t2 (Tmbin bSort s1 s2))
                  Id_ctx_nil
                  (alpha_extend_ids ([]) x2 (sub x t2 (Tmbin bSort s1 s2))
                    Id_ctx_nil
                    (alpha_trans x2 (Tmbin bSort x0 x1)
                      (sub x t2 (Tmbin bSort s1 s2)) ([]) ([]) ([])
                      Alpha_trans_nil a1 (Alpha_app bSort x0
                      (let {
                        sub0 x3 u t =
                          case t of {
                           Tmvar y ->
                            case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                   x3 y of {
                             Prelude.True -> u;
                             Prelude.False -> Tmvar y};
                           Tmabs b y k1 t' -> Tmabs b y k1 (sub0 x3 u t');
                           Tmbin b t3 t4 -> Tmbin b (sub0 x3 u t3)
                            (sub0 x3 u t4);
                           Tmbuiltin d -> Tmbuiltin d}}
                       in sub0 x t2 s1) x1
                      (let {
                        sub0 x3 u t =
                          case t of {
                           Tmvar y ->
                            case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                   x3 y of {
                             Prelude.True -> u;
                             Prelude.False -> Tmvar y};
                           Tmabs b y k1 t' -> Tmabs b y k1 (sub0 x3 u t');
                           Tmbin b t3 t4 -> Tmbin b (sub0 x3 u t3)
                            (sub0 x3 u t4);
                           Tmbuiltin d -> Tmbuiltin d}}
                       in sub0 x t2 s2) ([]) a a0)))))}}}}}}) (\d _ -> ExistT
    (sub x t1 (Tmbuiltin d)) ((,) (Red_gu_na_nil (sub x t1 (Tmbuiltin d)))
    (Alpha_builtin ([]) d))) s hNC_t1

data Reducible p =
   Build_reducible (Term0 -> p -> Sn Term0 Step_gu) (Term0 -> Term0 -> p ->
                                                    Step_gu -> p) (Term0 ->
                                                                  () ->
                                                                  (Term0 ->
                                                                  Step_gu ->
                                                                  p) -> p)

p_sn :: (Reducible a1) -> Term0 -> a1 -> Sn Term0 Step_gu
p_sn r =
  case r of {
   Build_reducible p_sn0 _ _ -> p_sn0}

p_cl :: (Reducible a1) -> Term0 -> Term0 -> a1 -> Step_gu -> a1
p_cl r =
  case r of {
   Build_reducible _ p_cl0 _ -> p_cl0}

p_nc :: (Reducible a1) -> Term0 -> (Term0 -> Step_gu -> a1) -> a1
p_nc r s x =
  case r of {
   Build_reducible _ _ p_nc0 -> p_nc0 s __ x}

type L = Any

_UU03b1__preserves_L_R :: Kind -> Term0 -> Term0 -> (([])
                          ((,) Prelude.String Prelude.String)) -> Alpha -> L
                          -> L
_UU03b1__preserves_L_R a s s' r x x0 =
  kind_rect (\r0 s'0 s0 h x1 ->
    unsafeCoerce _UU03b1__preserves_SN_R s0 s'0 r0 h x1)
    (\_ iHA1 _ iHA2 r0 s'0 s0 h x1 ->
    unsafeCoerce (\t' ht ->
      let {rt = a_constr (sym_alpha_ctx r0) s'0 s0 t'} in
      case rt of {
       (,) l t ->
        iHA2 (sym_alpha_ctx l) (Tmbin App s'0 t') (Tmbin App s0 t)
          (alpha_sym (Tmbin App s'0 t') (Tmbin App s0 t) l (sym_alpha_ctx l)
            (sym_alpha_ctx_is_sym l) (Alpha_app App s'0 s0 t' t l
            (alpha_sym s0 s'0 (sym_alpha_ctx l) l
              (sym_alpha_ctx_left_is_sym l)
              (alpha_sym s'0 s0 l (sym_alpha_ctx l) (sym_alpha_ctx_is_sym l)
                (a_constr__s_alpha (sym_alpha_ctx r0) s'0 s0 t' l t
                  (alpha_sym s0 s'0 r0 (sym_alpha_ctx r0)
                    (sym_alpha_ctx_is_sym r0) h))))
            (alpha_sym t t' (sym_alpha_ctx l) l (sym_alpha_ctx_left_is_sym l)
              (alpha_sym t' t l (sym_alpha_ctx l) (sym_alpha_ctx_is_sym l)
                (a_constr__t_alpha (sym_alpha_ctx r0) s'0 s0 t' l t
                  (alpha_sym s0 s'0 r0 (sym_alpha_ctx r0)
                    (sym_alpha_ctx_is_sym r0) h))))))
          (unsafeCoerce x1 t
            (iHA1 l t t'
              (alpha_sym t t' (sym_alpha_ctx l) l
                (sym_alpha_ctx_left_is_sym l)
                (alpha_sym t' t l (sym_alpha_ctx l) (sym_alpha_ctx_is_sym l)
                  (a_constr__t_alpha (sym_alpha_ctx r0) s'0 s0 t' l t
                    (alpha_sym s0 s'0 r0 (sym_alpha_ctx r0)
                      (sym_alpha_ctx_is_sym r0) h)))) ht))})) a r s' s x x0

reducible_sn :: Reducible (Sn Term0 Step_gu)
reducible_sn =
  Build_reducible (\_ x -> x) (\_ t __top_assumption_ ->
    let {_evar_0_ = \f0 _view_subject_ -> f0 t _view_subject_} in
    case __top_assumption_ of {
     SNI s -> _evar_0_ s}) (\s ->
    let {_evar_0_ = \_ x -> SNI x} in
    let {_evar_0_0 = \_ _ _ _ _ _ -> Prelude.error "absurd case"} in
    let {_evar_0_1 = \_ _ _ _ _ x -> SNI x} in
    let {_evar_0_2 = \_ x -> SNI x} in
    term_rect (\s0 _ x -> _evar_0_ s0 x) (\uSort s0 k t x _ x0 ->
      _evar_0_0 uSort s0 k t x x0) (\bSort t x t0 x0 _ x1 ->
      _evar_0_1 bSort t x t0 x0 x1) (\d _ x -> _evar_0_2 d x) s)

reducible_var :: Prelude.String -> (Reducible a1) -> a1
reducible_var x _view_subject_ =
  let {_top_assumption_ = \x0 -> p_nc _view_subject_ x0} in
  let {_evar_0_ = \_ _ -> Prelude.error "absurd case"} in
  _top_assumption_ (Tmvar x) _evar_0_

l_reducible :: Kind -> Reducible L
l_reducible a =
  let {
   _evar_0_ = \a0 ih1 b ih2 -> Build_reducible (\s h ->
    sn_closedL App (Tmvar "x") s
      (p_sn ih2 (Tmbin App s (Tmvar "x"))
        (h (Tmvar "x") (reducible_var "x" ih1)))) (\s t x x0 t0 x1 ->
    let {x2 = x t0 x1} in
    let {h = step_gu_app_l App s t0 t x0} in
    case h of {
     ExistT x3 p ->
      case p of {
       (,) a1 s0 ->
        case s0 of {
         ExistT x4 p0 ->
          case p0 of {
           (,) a2 s1 ->
            let {x5 = p_cl ih2 (Tmbin App s t0) (Tmbin App x3 x4) x2 s1} in
            _UU03b1__preserves_L_R b (Tmbin App x3 x4) (Tmbin App t t0) ([])
              (Alpha_app App x3 t x4 t0 ([])
              (alpha_sym t x3 ([]) ([]) Alpha_sym_nil a1)
              (alpha_sym t0 x4 ([]) ([]) Alpha_sym_nil a2)) x5}}}})
    (\s _ h t la ->
    ssr_have_upoly (p_sn ih1 t la) (\snt ->
      let {
       _evar_0_ = \t0 _ ih3 la0 ->
        p_nc ih2 (Tmbin App s t0) (\_ st ->
          case st of {
           Step_gu_intro _ _ _ x x0 x1 ->
            case x of {
             Alpha_app _ _ s2 _ t2 _ x2 x3 ->
              case x1 of {
               Step_appL0 _ _ s3 _ x4 ->
                let {la1 = _UU03b1__preserves_L_R a0 t0 t2 ([]) x3 la0} in
                let {h0 = gu_app_l App s2 t2 x0} in
                h s3 (Step_gu_intro s s2 s3 x2 h0 x4) t2 la1;
               Step_appR0 _ _ _ t3 x4 ->
                let {
                 h0 = let {h0 = gu_app_r App s2 t2 x0} in
                      Step_gu_intro t0 t2 t3 x3 h0 x4}
                in
                let {ih4 = ih3 t3 h0} in
                _UU03b1__preserves_L_R b (Tmbin App s t3) (Tmbin App s2 t3)
                  ([]) (Alpha_app App s s2 t3 t3 ([]) x2
                  (alpha_refl t3 ([]) Alpha_refl_nil))
                  (let {h1 = p_cl ih1 t0 t3 la0 h0} in ih4 h1);
               _ -> Prelude.error "absurd case"};
             _ -> Prelude.error "absurd case"}})}
      in
      sn_rect _evar_0_ t snt la))}
  in
  kind_rect (unsafeCoerce reducible_sn) (unsafeCoerce _evar_0_) a

l_sn :: Kind -> Term0 -> L -> Sn Term0 Step_gu
l_sn a s las =
  let {x = l_reducible a} in p_sn x s las

l_cl :: Kind -> Term0 -> Term0 -> L -> Step_gu -> L
l_cl t s t0 hstep hst =
  let {h = l_reducible t} in p_cl h s t0 hstep hst

l_nc :: Kind -> Term0 -> (Term0 -> Step_gu -> L) -> L
l_nc t s hstep =
  let {h = l_reducible t} in p_nc h s hstep

l_var :: Kind -> Prelude.String -> L
l_var t x =
  l_nc t (Tmvar x) (\_ _ -> Prelude.error "absurd case")

l_cl_star :: Kind -> Term0 -> Term0 -> L -> Red_gu_na -> L
l_cl_star t s t0 ls red_st =
  red_gu_na_rect (\s0 t1 _ s1 _ iHred_st ls0 ->
    iHred_st (l_cl t s0 t1 ls0 s1)) (\_ ls0 -> ls0) s t0 red_st ls

beta_expansion' :: BSort -> USort -> Kind -> Kind -> Prelude.String ->
                   Prelude.String -> Term0 -> Term0 -> Term0 -> Alpha -> GU
                   -> NC -> (Sn Term0 Step_gu) -> L -> L
beta_expansion' bA bL a b x y s s' t ha_s' gu nc snt h =
  let {
   hsns' = _UU03b1__preserves_SN_R s s' (sym_alpha_ctx ((:) ((,) y x) ([])))
             (alpha_sym s' s
               (sym_alpha_ctx (sym_alpha_ctx ((:) ((,) y x) ([]))))
               (sym_alpha_ctx ((:) ((,) y x) ([])))
               (sym_alpha_ctx_left_is_sym
                 (sym_alpha_ctx ((:) ((,) y x) ([]))))
               (alpha_sym s s' (sym_alpha_ctx ((:) ((,) y x) ([])))
                 (sym_alpha_ctx (sym_alpha_ctx ((:) ((,) y x) ([]))))
                 (sym_alpha_ctx_is_sym (sym_alpha_ctx ((:) ((,) y x) ([]))))
                 (alpha_sym s' s ((:) ((,) y x) ([]))
                   (sym_alpha_ctx ((:) ((,) y x) ([])))
                   (sym_alpha_ctx_is_sym ((:) ((,) y x) ([]))) ha_s')))
             (sn_subst x t s nc (l_sn a (sub x t s) h))}
  in
  sn_rect (\x0 _ iH1 t0 snt0 s0 ha hnc ->
    sn_rect (\x1 s1 iH2 hgu hnc0 hL ->
      l_nc a (Tmbin bA (Tmabs bL y b x0) x1) (\_ st ->
        case st of {
         Step_gu_intro _ _ _ x2 x3 x4 ->
          case x2 of {
           Alpha_app _ _ _ _ t2 _ x5 x6 ->
            case x5 of {
             Alpha_lam _ _ y0 _ _ s2 _ x7 ->
              case x4 of {
               Step_beta0 _ _ _ _ ->
                _UU03b1__preserves_L_R a (sub x x1 s0) (sub y0 t2 s2) ([])
                  (alpha_rename_binder_stronger x y0 s0 x1 t2 ([]) s2 ((:)
                    ((,) x y0) ([]))
                    (alpha_sym s2 s0 (sym_alpha_ctx ((:) ((,) x y0) ([])))
                      ((:) ((,) x y0) ([]))
                      (sym_alpha_ctx_left_is_sym ((:) ((,) x y0) ([])))
                      (alpha_trans s2 x0 s0 ((:) ((,) y0 y) ([])) ((:) ((,) y
                        x) ([])) (sym_alpha_ctx ((:) ((,) x y0) ([])))
                        (Alpha_trans_cons y0 y x ([]) ([]) ([])
                        Alpha_trans_nil)
                        (alpha_sym x0 s2
                          (sym_alpha_ctx ((:) ((,) y0 y) ([]))) ((:) ((,) y0
                          y) ([]))
                          (sym_alpha_ctx_left_is_sym ((:) ((,) y0 y) ([])))
                          x7) ha)) x6 StarR hnc0
                    (gu_applam_to_nc App Lam s2 t2 y0 b x3)) hL;
               Step_appL0 _ _ _ _ x8 ->
                case x8 of {
                 Step_abs0 _ _ _ _ s3 x9 ->
                  let {
                   h0 = step_naive_preserves_alpha2 s2 s3 (to_GU x0) ((:)
                          ((,) y0 y) ([]))
                          (gu_lam bL y0 b s2
                            (gu_app_l bA (Tmabs bL y0 b s2) t2 x3))
                          (to_GU__GU x0)
                          (alpha_trans s2 x0 (to_GU x0) ((:) ((,) y0 y) ([]))
                            ((:) ((,) y y) ([])) ((:) ((,) y0 y) ([]))
                            (Alpha_trans_cons y0 y y ([]) ([]) ([])
                            Alpha_trans_nil)
                            (alpha_sym x0 s2
                              (sym_alpha_ctx ((:) ((,) y0 y) ([]))) ((:) ((,)
                              y0 y) ([]))
                              (sym_alpha_ctx_left_is_sym ((:) ((,) y0 y)
                                ([]))) x7)
                            (alpha_extend_ids ((:) ((,) y y) ([])) x0
                              (to_GU x0) (Id_ctx_cons y ([]) Id_ctx_nil)
                              (to_GU__alpha x0))) x9}
                  in
                  case h0 of {
                   ExistT x10 p ->
                    case p of {
                     (,) s4 a0 ->
                      let {
                       hstep_na_s5' = Step_gu_intro x0 (to_GU x0) x10
                        (to_GU__alpha x0) (to_GU__GU x0) s4}
                      in
                      _UU03b1__preserves_L_R a (Tmbin bA (Tmabs bL y b x10)
                        x1) (Tmbin bA (Tmabs bL y0 b s3) t2) ([])
                        (alpha_extend_ids ([]) (Tmbin bA (Tmabs bL y b x10)
                          x1) (Tmbin bA (Tmabs bL y0 b s3) t2) Id_ctx_nil
                          (Alpha_app bA (Tmabs bL y b x10) (Tmabs bL y0 b s3)
                          x1 t2 ([]) (Alpha_lam bL y y0 b x10 s3 ([])
                          (alpha_sym s3 x10
                            (sym_alpha_ctx ((:) ((,) y y0) ([]))) ((:) ((,) y
                            y0) ([]))
                            (sym_alpha_ctx_left_is_sym ((:) ((,) y y0) ([])))
                            a0)) x6))
                        (let {iH3 = iH1 x10 hstep_na_s5'} in
                         case hstep_na_s5' of {
                          Step_gu_intro _ s'0 _ x11 x12 x13 ->
                           let {
                            s5 = step_naive_preserves_alpha2 s'0 x10 s0 ((:)
                                   ((,) y x) ([])) x12 hgu
                                   (alpha_trans s'0 x0 s0 ((:) ((,) y y)
                                     ([])) ((:) ((,) y x) ([])) ((:) ((,) y
                                     x) ([])) (Alpha_trans_cons y y x ([])
                                     ([]) ([]) Alpha_trans_nil)
                                     (alpha_extend_ids ((:) ((,) y y) ([]))
                                       s'0 x0 (Id_ctx_cons y ([]) Id_ctx_nil)
                                       (alpha_extend_ids ([]) s'0 x0
                                         Id_ctx_nil
                                         (alpha_sym x0 s'0
                                           (sym_alpha_ctx ([])) ([])
                                           (sym_alpha_ctx_left_is_sym ([]))
                                           x11))) ha) x13}
                           in
                           case s5 of {
                            ExistT x14 p0 ->
                             case p0 of {
                              (,) s6 a1 ->
                               iH3 x1 (SNI s1) (to_GU' x x1 x14)
                                 (alpha_trans x10 x14 (to_GU' x x1 x14) ((:)
                                   ((,) y x) ([])) ((:) ((,) x x) ([])) ((:)
                                   ((,) y x) ([])) (Alpha_trans_cons y x x
                                   ([]) ([]) ([]) Alpha_trans_nil) a1
                                   (alpha_extend_ids ((:) ((,) x x) ([])) x14
                                     (to_GU' x x1 x14) (Id_ctx_cons x ([])
                                     Id_ctx_nil) (to_GU'__alpha x x1 x14)))
                                 (to_GU'__GU x x1 x14) (to_GU'__NC x x1 x14)
                                 (let {
                                   h3 = step_subst_single ([]) x x1 s0 x14
                                          (to_GU' x x1 x14) s6 hgu hnc0
                                          (to_GU'__alpha x x1 x14)
                                          (Alpha_ctx_cons ([]) ([]) ([]) x x
                                          x1 x1 (Alpha_ctx_nil ([]))
                                          (Alpha_var_refl x)
                                          (alpha_refl x1 ([]) Alpha_refl_nil))
                                          (to_GU'__NC x x1 x14)}
                                  in
                                  case h3 of {
                                   ExistT x15 p1 ->
                                    case p1 of {
                                     (,) s7 a2 ->
                                      _UU03b1__preserves_L_R a x15
                                        (sub x x1 (to_GU' x x1 x14)) ([]) a2
                                        (l_cl a (sub x x1 s0) x15 hL s7)}})}}})}};
                 _ -> Prelude.error "absurd case"};
               Step_appR0 _ _ _ t3 x8 ->
                _UU03b1__preserves_L_R a (Tmbin bA (Tmabs bL y b x0) t3)
                  (Tmbin bA (Tmabs bL y0 b s2) t3) ([])
                  (alpha_extend_ids ([]) (Tmbin bA (Tmabs bL y b x0) t3)
                    (Tmbin bA (Tmabs bL y0 b s2) t3) Id_ctx_nil
                    (alpha_extend_ids ([]) (Tmbin bA (Tmabs bL y b x0) t3)
                      (Tmbin bA (Tmabs bL y0 b s2) t3) Id_ctx_nil (Alpha_app
                      bA (Tmabs bL y b x0) (Tmabs bL y0 b s2) t3 t3 ([]) x5
                      (alpha_refl t3 ([]) Alpha_refl_nil))))
                  (iH2 t3 (Step_gu_intro x1 t2 t3 x6
                    (gu_app_r bA (Tmabs bL y0 b s2) t2 x3) x8) hgu
                    (step_naive_preserves_nc_ctx s0 t2 t3 x x8
                      (alpha_preserves_nc_ctx s0 x x1 t2 x6 hnc0))
                    (let {
                      s3 = red_beta x s0 x1 t3 (Step_gu_intro x1 t2 t3 x6
                             (gu_app_r bA (Tmabs bL y0 b s2) t2 x3) x8) hnc0}
                     in
                     case s3 of {
                      ExistT x9 p ->
                       case p of {
                        (,) r a0 ->
                         let {hL0 = l_cl_star a (sub x x1 s0) x9 hL r} in
                         _UU03b1__preserves_L_R a x9 (sub x t3 s0) ([]) a0
                           hL0}}));
               Step_abs0 _ _ _ _ _ _ -> Prelude.error "absurd case"};
             _ -> Prelude.error "absurd case"};
           _ -> Prelude.error "absurd case"}})) t0 snt0 hnc) s' hsns' t snt s
    ha_s' gu nc h

type EL = Prelude.String -> Kind -> () -> SigT Term0 ((,) () L)

extend_EL :: (([]) ((,) Prelude.String Kind)) -> (([])
             ((,) Prelude.String Term0)) -> Prelude.String -> Kind -> Term0
             -> EL -> L -> Prelude.String -> Kind -> SigT Term0 ((,) () L)
extend_EL _ _ x _ t hEL hL x0 t0 =
  let {
   b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x0
         x}
  in
  case b of {
   Prelude.True -> ExistT t ((,) __ hL);
   Prelude.False ->
    let {hEL0 = hEL x0 t0 __} in
    case hEL0 of {
     ExistT x1 p -> case p of {
                     (,) _ l -> ExistT x1 ((,) __ l)}}}

beta_expansion_subst :: BSort -> USort -> Prelude.String -> Term0 -> (([])
                        ((,) Prelude.String Term0)) -> Term0 -> Kind -> Kind
                        -> ParSeq -> NC -> (Sn Term0 Step_gu) -> L -> L
beta_expansion_subst bA bL x t sigma s a b _ nc snt hL =
  _UU03b1__preserves_L_R a (Tmbin bA (Tmabs bL x b
    (to_GU' x t (psubs sigma s))) t) (Tmbin bA (psubs sigma (Tmabs bL x b s))
    t) ([]) (Alpha_app bA (Tmabs bL x b (to_GU' x t (psubs sigma s)))
    (psubs sigma (Tmabs bL x b s)) t t ([]) (Alpha_lam bL x x b
    (to_GU' x t (psubs sigma s))
    (let {
      psubs0 sigma0 t0 =
        case t0 of {
         Tmvar x0 ->
          case lookup x0 sigma0 of {
           Prelude.Just t1 -> t1;
           Prelude.Nothing -> Tmvar x0};
         Tmabs b0 x0 a0 s0 -> Tmabs b0 x0 a0 (psubs0 sigma0 s0);
         Tmbin b0 s0 t1 -> Tmbin b0 (psubs0 sigma0 s0) (psubs0 sigma0 t1);
         Tmbuiltin d -> Tmbuiltin d}}
     in psubs0 sigma s) ([])
    (alpha_extend_ids ((:) ((,) x x) ([])) (to_GU' x t (psubs sigma s))
      (let {
        psubs0 sigma0 t0 =
          case t0 of {
           Tmvar x0 ->
            case lookup x0 sigma0 of {
             Prelude.Just t1 -> t1;
             Prelude.Nothing -> Tmvar x0};
           Tmabs b0 x0 a0 s0 -> Tmabs b0 x0 a0 (psubs0 sigma0 s0);
           Tmbin b0 s0 t1 -> Tmbin b0 (psubs0 sigma0 s0) (psubs0 sigma0 t1);
           Tmbuiltin d -> Tmbuiltin d}}
       in psubs0 sigma s) (Id_ctx_cons x ([]) Id_ctx_nil)
      (alpha_sym
        (let {
          psubs0 sigma0 t0 =
            case t0 of {
             Tmvar x0 ->
              case lookup x0 sigma0 of {
               Prelude.Just t1 -> t1;
               Prelude.Nothing -> Tmvar x0};
             Tmabs b0 x0 a0 s0 -> Tmabs b0 x0 a0 (psubs0 sigma0 s0);
             Tmbin b0 s0 t1 -> Tmbin b0 (psubs0 sigma0 s0) (psubs0 sigma0 t1);
             Tmbuiltin d -> Tmbuiltin d}}
         in psubs0 sigma s) (to_GU' x t (psubs sigma s)) (sym_alpha_ctx ([]))
        ([]) (sym_alpha_ctx_left_is_sym ([]))
        (to_GU'__alpha x t (psubs sigma s)))))
    (alpha_refl t ([]) Alpha_refl_nil))
    (let {
      hL0 = _UU03b1__preserves_L_R a (psubs ((:) ((,) x t) sigma) s)
              (sub x t (to_GU' x t (psubs sigma s))) ([])
              (let {
                _evar_0_ = psubs___UU03b1_ (psubs sigma s) ([])
                             (to_GU' x t (psubs sigma s)) ((:) ((,) x t)
                             ([])) ((:) ((,) x t) ([])) nc
                             (to_GU'__NC x t (psubs sigma s))
                             (to_GU'__alpha x t (psubs sigma s))
                             (Alpha_ctx_cons ([]) ([]) ([]) x x t t
                             (Alpha_ctx_nil ([])) (Alpha_var_refl x)
                             (alpha_refl t ([]) Alpha_refl_nil))}
               in
               eq_rec_r (psubs ((:) ((,) x t) ([])) (psubs sigma s)) _evar_0_
                 (psubs ((:) ((,) x t) sigma) s)) hL}
     in
     beta_expansion' bA bL a b x x (to_GU' x t (psubs sigma s))
       (to_GU' x t (psubs sigma s)) t
       (alpha_refl (to_GU' x t (psubs sigma s)) ((:) ((,) x x) ([]))
         (Alpha_refl_cons x ([]) Alpha_refl_nil))
       (to_GU'__GU x t (psubs sigma s)) (to_GU'__NC x t (psubs sigma s)) snt
       hL0)

fundamental :: (([]) ((,) BinderTyname Kind)) -> Term0 -> Kind -> Has_kind ->
               GU -> (([]) ((,) Prelude.String Term0)) -> NC -> ParSeq -> EL
               -> L
fundamental _UU0394_ s a _top_assumption_ x sigma x0 x1 x2 =
  let {
   _evar_0_ = \_ x3 a0 _ _ _ _ hEL ->
    let {s0 = hEL x3 a0 __} in
    case s0 of {
     ExistT _ p -> case p of {
                    (,) _ l -> l}}}
  in
  let {
   _evar_0_0 = \_ t1 t2 _ x3 _ x4 x5 sigma0 x6 x7 x8 ->
    sn_ty_fun Fun
      (let {
        psubs0 sigma1 t =
          case t of {
           Tmvar x9 ->
            case lookup x9 sigma1 of {
             Prelude.Just t0 -> t0;
             Prelude.Nothing -> Tmvar x9};
           Tmabs b x9 a0 s0 -> Tmabs b x9 a0 (psubs0 sigma1 s0);
           Tmbin b s0 t0 -> Tmbin b (psubs0 sigma1 s0) (psubs0 sigma1 t0);
           Tmbuiltin d -> Tmbuiltin d}}
       in psubs0 sigma0 t1)
      (let {
        psubs0 sigma1 t =
          case t of {
           Tmvar x9 ->
            case lookup x9 sigma1 of {
             Prelude.Just t0 -> t0;
             Prelude.Nothing -> Tmvar x9};
           Tmabs b x9 a0 s0 -> Tmabs b x9 a0 (psubs0 sigma1 s0);
           Tmbin b s0 t0 -> Tmbin b (psubs0 sigma1 s0) (psubs0 sigma1 t0);
           Tmbuiltin d -> Tmbuiltin d}}
       in psubs0 sigma0 t2)
      (x3 (gu_app_l Fun t1 t2 x5) sigma0 __ (nc_app_l Fun t1 t2 sigma0 x6) x7
        x8)
      (x4 (gu_app_r Fun t1 t2 x5) sigma0 __ (nc_app_r Fun t1 t2 sigma0 x6) x7
        x8)}
  in
  let {
   _evar_0_1 = \_ f0 t k _ x3 _ x4 x5 sigma0 x6 x7 x8 ->
    sn_ty_fun IFix
      (let {
        psubs0 sigma1 t0 =
          case t0 of {
           Tmvar x9 ->
            case lookup x9 sigma1 of {
             Prelude.Just t1 -> t1;
             Prelude.Nothing -> Tmvar x9};
           Tmabs b x9 a0 s0 -> Tmabs b x9 a0 (psubs0 sigma1 s0);
           Tmbin b s0 t1 -> Tmbin b (psubs0 sigma1 s0) (psubs0 sigma1 t1);
           Tmbuiltin d -> Tmbuiltin d}}
       in psubs0 sigma0 f0)
      (let {
        psubs0 sigma1 t0 =
          case t0 of {
           Tmvar x9 ->
            case lookup x9 sigma1 of {
             Prelude.Just t1 -> t1;
             Prelude.Nothing -> Tmvar x9};
           Tmabs b x9 a0 s0 -> Tmabs b x9 a0 (psubs0 sigma1 s0);
           Tmbin b s0 t1 -> Tmbin b (psubs0 sigma1 s0) (psubs0 sigma1 t1);
           Tmbuiltin d -> Tmbuiltin d}}
       in psubs0 sigma0 t)
      (l_sn (Kind_Arrow (Kind_Arrow k Kind_Base) (Kind_Arrow k Kind_Base))
        (let {
          psubs0 sigma1 t0 =
            case t0 of {
             Tmvar x9 ->
              case lookup x9 sigma1 of {
               Prelude.Just t1 -> t1;
               Prelude.Nothing -> Tmvar x9};
             Tmabs b x9 a0 s0 -> Tmabs b x9 a0 (psubs0 sigma1 s0);
             Tmbin b s0 t1 -> Tmbin b (psubs0 sigma1 s0) (psubs0 sigma1 t1);
             Tmbuiltin d -> Tmbuiltin d}}
         in psubs0 sigma0 f0)
        (x4 (gu_app_l IFix f0 t x5) sigma0 __ (nc_app_l IFix f0 t sigma0 x6)
          x7 x8))
      (l_sn k
        (let {
          psubs0 sigma1 t0 =
            case t0 of {
             Tmvar x9 ->
              case lookup x9 sigma1 of {
               Prelude.Just t1 -> t1;
               Prelude.Nothing -> Tmvar x9};
             Tmabs b x9 a0 s0 -> Tmabs b x9 a0 (psubs0 sigma1 s0);
             Tmbin b s0 t1 -> Tmbin b (psubs0 sigma1 s0) (psubs0 sigma1 t1);
             Tmbuiltin d -> Tmbuiltin d}}
         in psubs0 sigma0 t)
        (x3 (gu_app_r IFix f0 t x5) sigma0 __ (nc_app_r IFix f0 t sigma0 x6)
          x7 x8))}
  in
  let {
   _evar_0_2 = \_UU0394_0 x3 k t _ x4 x5 sigma0 x6 x7 x8 ->
    sn_ty_forall ForAll x3 k
      (let {
        psubs0 sigma1 t0 =
          case t0 of {
           Tmvar x9 ->
            case lookup x9 sigma1 of {
             Prelude.Just t1 -> t1;
             Prelude.Nothing -> Tmvar x9};
           Tmabs b x9 a0 s0 -> Tmabs b x9 a0 (psubs0 sigma1 s0);
           Tmbin b s0 t1 -> Tmbin b (psubs0 sigma1 s0) (psubs0 sigma1 t1);
           Tmbuiltin d -> Tmbuiltin d}}
       in psubs0 sigma0 t)
      (x4 (gu_lam ForAll x3 k t x5) ((:) ((,) x3 (Tmvar x3)) sigma0) __
        (Nc_cons t x3 (Tmvar x3) sigma0 (nc_lam ForAll x3 t k sigma0 x6))
        (ParSeq_cons x3 (Tmvar x3) sigma0 x7) (\x9 x10 _ ->
        extend_EL _UU0394_0 sigma0 x3 k (Tmvar x3) x8 (l_var k x3) x9 x10))}
  in
  let {
   _evar_0_3 = \_ _ _ _ _ _ _ -> SNI (\_ _ -> Prelude.error "absurd case")}
  in
  let {
   _evar_0_4 = \_UU0394_0 x3 a0 s0 b _ ih gu sigma0 nc ps eL t hLA ->
    let {t'R = t_constr t s0 sigma0 x3} in
    case t'R of {
     (,) t0 l ->
      let {hparseq = ParSeq_cons x3 t0 sigma0 ps} in
      let {
       ih0 = ih (gu_lam Lam x3 a0 s0 gu) ((:) ((,) x3 t0) sigma0) __
               (t_constr__nc_s t t0 l s0 sigma0 x3
                 (nc_lam Lam x3 s0 a0 sigma0 nc)) hparseq (\x4 x5 _ ->
               extend_EL _UU0394_0 sigma0 x3 a0 t0 eL
                 (_UU03b1__preserves_L_R a0 t t0 l
                   (t_constr__a_t t t0 l s0 sigma0 x3) hLA) x4 x5)}
      in
      let {
       ih1 = beta_expansion_subst App Lam x3 t0 sigma0 s0 b a0 hparseq
               (t_constr__nc_subs t t0 l s0 sigma0 x3)
               (_UU03b1__preserves_SN_R t t0 l
                 (t_constr__a_t t t0 l s0 sigma0 x3) (l_sn a0 t hLA)) ih0}
      in
      _UU03b1__preserves_L_R b (Tmbin App (psubs sigma0 (Tmabs Lam x3 a0 s0))
        t0) (Tmbin App (psubs sigma0 (Tmabs Lam x3 a0 s0)) t)
        (sym_alpha_ctx l) (Alpha_app App (psubs sigma0 (Tmabs Lam x3 a0 s0))
        (psubs sigma0 (Tmabs Lam x3 a0 s0)) t0 t (sym_alpha_ctx l)
        (alpha_sym (psubs sigma0 (Tmabs Lam x3 a0 s0))
          (psubs sigma0 (Tmabs Lam x3 a0 s0)) l (sym_alpha_ctx l)
          (sym_alpha_ctx_is_sym l)
          (psubs___UU03b1_ (Tmabs Lam x3 a0 s0) l (Tmabs Lam x3 a0 s0) sigma0
            sigma0 nc nc (Alpha_lam Lam x3 x3 a0 s0 s0 l
            (alpha_extend_id'' s0 x3 l
              (t_constr__a_s t t0 l s0 sigma0 x3 (gu_lam Lam x3 a0 s0 gu))))
            (t_constr__a_sigma t t0 l s0 sigma0 x3
              (nc_lam Lam x3 s0 a0 sigma0 nc))))
        (alpha_sym t t0 l (sym_alpha_ctx l) (sym_alpha_ctx_is_sym l)
          (t_constr__a_t t t0 l s0 sigma0 x3))) ih1}}
  in
  let {
   _evar_0_5 = \_ s0 t _ _ _ ih1 _ ih2 gu sigma0 nc ps hEL ->
    ih1 (gu_app_l App s0 t gu) sigma0 __ (nc_app_l App s0 t sigma0 nc) ps hEL
      (let {
        psubs0 sigma1 t0 =
          case t0 of {
           Tmvar x3 ->
            case lookup x3 sigma1 of {
             Prelude.Just t1 -> t1;
             Prelude.Nothing -> Tmvar x3};
           Tmabs b x3 a0 s1 -> Tmabs b x3 a0 (psubs0 sigma1 s1);
           Tmbin b s1 t1 -> Tmbin b (psubs0 sigma1 s1) (psubs0 sigma1 t1);
           Tmbuiltin d -> Tmbuiltin d}}
       in psubs0 sigma0 t)
      (ih2 (gu_app_r App s0 t gu) sigma0 __ (nc_app_r App s0 t sigma0 nc) ps
        hEL)}
  in
  has_kind_rect (\_UU0394_0 x3 a0 _ gu sigma0 _ nc ->
    _evar_0_ _UU0394_0 x3 a0 gu sigma0 nc)
    (\_UU0394_0 t1 t2 h x3 h0 x4 x5 sigma0 _ x6 ->
    unsafeCoerce _evar_0_0 _UU0394_0 t1 t2 h x3 h0 x4 x5 sigma0 x6)
    (\_UU0394_0 f0 t k h x3 h0 x4 x5 sigma0 _ x6 ->
    unsafeCoerce _evar_0_1 _UU0394_0 f0 t k h x3 h0 x4 x5 sigma0 x6)
    (\_UU0394_0 x3 k t h x4 x5 sigma0 _ x6 ->
    unsafeCoerce _evar_0_2 _UU0394_0 x3 k t h x4 x5 sigma0 x6)
    (\_UU0394_0 t _ x3 sigma0 _ x4 ->
    unsafeCoerce _evar_0_3 _UU0394_0 t x3 sigma0 x4)
    (\_UU0394_0 x3 a0 s0 b _H ih gu sigma0 _ nc ->
    unsafeCoerce _evar_0_4 _UU0394_0 x3 a0 s0 b _H ih gu sigma0 nc)
    (\_UU0394_0 s0 t a0 b _H ih1 _H0 ih2 gu sigma0 _ nc ->
    unsafeCoerce _evar_0_5 _UU0394_0 s0 t a0 b _H ih1 _H0 ih2 gu sigma0 nc)
    _UU0394_ s a _top_assumption_ x sigma __ x0 x1 x2

id_subst__EL :: (([]) ((,) Prelude.String Kind)) -> Prelude.String -> Kind ->
                SigT Term0 ((,) () L)
id_subst__EL _UU0394_ x t =
  list_rect (\_ _ _ -> Prelude.error "absurd case")
    (\a _UU0394_0 iH_UU0394_ x0 x1 _ ->
    case a of {
     (,) s k ->
      extend_EL _UU0394_0 (id_subst _UU0394_0) s k (Tmvar s) iH_UU0394_
        (l_var k s) x0 x1}) _UU0394_ x t __

type_L :: (([]) ((,) BinderTyname Kind)) -> Term0 -> Kind -> Has_kind -> L
type_L _UU0394_ s t hkind =
  let {s' = s_constr s (id_subst _UU0394_)} in
  let {
   hkind0 = alpha_preserves_typing ([]) s s' t _UU0394_ _UU0394_
              (s_constr__a_s s s' (id_subst _UU0394_)) hkind}
  in
  let {
   hkind1 = fundamental _UU0394_ s' t hkind0
              (s_constr__gu s s' (id_subst _UU0394_)) (id_subst _UU0394_)
              (s_constr__nc_s s s' (id_subst _UU0394_))
              (id_subst__ParSeq (id_subst _UU0394_)
                (id_subst_is_IdSubst _UU0394_)) (\x x0 _ ->
              id_subst__EL _UU0394_ x x0)}
  in
  _UU03b1__preserves_L_R t s' s ([])
    (alpha_extend_ids ([]) s' s Id_ctx_nil
      (alpha_extend_ids ([]) s' s Id_ctx_nil
        (alpha_sym s s' (sym_alpha_ctx ([])) ([])
          (sym_alpha_ctx_left_is_sym ([]))
          (s_constr__a_s s s' (id_subst _UU0394_))))) hkind1

strong_normalization_gu :: (([]) ((,) BinderTyname Kind)) -> Term0 -> Kind ->
                           Has_kind -> Sn Term0 Step_gu
strong_normalization_gu _UU0394_ s t hkind =
  let {hkind0 = type_L _UU0394_ s t hkind} in l_sn t s hkind0

bvc :: Vdecl -> Name
bvc c =
  case c of {
   VarDecl x _ -> x}

bvb :: Binding -> ([]) BinderName
bvb b =
  case b of {
   TermBind _ v _ -> case v of {
                      VarDecl x _ -> (:) x ([])};
   TypeBind _ _ -> ([]);
   DatatypeBind d ->
    case d of {
     Datatype _ _ matchFunc cs -> (:) matchFunc (rev0 (map bvc cs))}}

bvbs :: (([]) Binding) -> ([]) Name
bvbs bs =
  concat (map bvb bs)

btvb :: Binding -> ([]) Tyname
btvb b =
  case b of {
   TermBind _ _ _ -> ([]);
   TypeBind t _ -> case t of {
                    TyVarDecl x _ -> (:) x ([])};
   DatatypeBind d ->
    case d of {
     Datatype t _ _ _ -> case t of {
                          TyVarDecl x _ -> (:) x ([])}}}

btvbs :: (([]) Binding) -> ([]) Tyname
btvbs bs =
  concat (map btvb bs)

ftv1 :: Ty -> ([]) Prelude.String
ftv1 t =
  case t of {
   Ty_Var x -> (:) x ([]);
   Ty_Fun t1 t2 -> app (ftv1 t1) (ftv1 t2);
   Ty_IFix f0 t0 -> app (ftv1 f0) (ftv1 t0);
   Ty_Forall x _ t' ->
    remove ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
      x (ftv1 t');
   Ty_Builtin _ -> ([]);
   Ty_Lam x _ t' ->
    remove ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
      x (ftv1 t');
   Ty_App t1 t2 -> app (ftv1 t1) (ftv1 t2);
   Ty_SOP tss -> flatmap2 ftv1 tss}

data Step_nd =
   Step_beta_nd Prelude.String Kind Term0 Term0
 | Step_appL_nd BSort Term0 Term0 Term0 Step_nd
 | Step_appR_nd BSort Term0 Term0 Term0 Step_nd
 | Step_abs_nd USort Prelude.String Kind Term0 Term0 Step_nd

step_nd_rect :: (Prelude.String -> Kind -> Term0 -> Term0 -> a1) -> (BSort ->
                Term0 -> Term0 -> Term0 -> Step_nd -> a1 -> a1) -> (BSort ->
                Term0 -> Term0 -> Term0 -> Step_nd -> a1 -> a1) -> (USort ->
                Prelude.String -> Kind -> Term0 -> Term0 -> Step_nd -> a1 ->
                a1) -> Term0 -> Term0 -> Step_nd -> a1
step_nd_rect f0 f1 f2 f3 _ _ s =
  case s of {
   Step_beta_nd x a s0 t -> f0 x a s0 t;
   Step_appL_nd b s1 s2 t s0 ->
    f1 b s1 s2 t s0 (step_nd_rect f0 f1 f2 f3 s1 s2 s0);
   Step_appR_nd b s0 t1 t2 s1 ->
    f2 b s0 t1 t2 s1 (step_nd_rect f0 f1 f2 f3 t1 t2 s1);
   Step_abs_nd b x a s1 s2 s0 ->
    f3 b x a s1 s2 s0 (step_nd_rect f0 f1 f2 f3 s1 s2 s0)}

step_nd_rec :: (Prelude.String -> Kind -> Term0 -> Term0 -> a1) -> (BSort ->
               Term0 -> Term0 -> Term0 -> Step_nd -> a1 -> a1) -> (BSort ->
               Term0 -> Term0 -> Term0 -> Step_nd -> a1 -> a1) -> (USort ->
               Prelude.String -> Kind -> Term0 -> Term0 -> Step_nd -> a1 ->
               a1) -> Term0 -> Term0 -> Step_nd -> a1
step_nd_rec =
  step_nd_rect

gU_step_d_implies_step_na :: Term0 -> Term0 -> GU -> Step_nd -> Step_naive
gU_step_d_implies_step_na t t' hGU_vars hstep =
  step_nd_rec (\x a s t0 _ ->
    let {_evar_0_ = Step_beta0 x a s t0} in
    eq_rec_r (sub x t0 s) _evar_0_ (substituteTCA0 x t0 s))
    (\b s1 s2 t0 _ iHHstep hGU_vars0 -> Step_appL0 b s1 s2 t0
    (case hGU_vars0 of {
      GU_app b0 s t1 x x0 ->
       eq_rec_r b (\_ ->
         eq_rec_r s1 (\_ -> eq_rec_r t0 (\h1 _ _ _ -> iHHstep h1) t1) s) b0
         __ __ x x0 __ __;
      GU_lam _ _ _ _ x -> false_rec x __;
      _ -> false_rec})) (\b s t1 t2 _ iHHstep hGU_vars0 -> Step_appR0 b s t1
    t2
    (case hGU_vars0 of {
      GU_app b0 s0 t0 x x0 ->
       eq_rec_r b (\_ ->
         eq_rec_r s (\_ -> eq_rec_r t1 (\_ h3 _ _ -> iHHstep h3) t0) s0) b0
         __ __ x x0 __ __;
      GU_lam _ _ _ _ x -> false_rec x __;
      _ -> false_rec})) (\b x a s1 s2 _ iHHstep hGU_vars0 -> Step_abs0 b x a
    s1 s2
    (case hGU_vars0 of {
      GU_app _ _ _ x0 x1 -> false_rec x0 x1 __ __;
      GU_lam b0 x0 a0 s x1 ->
       eq_rec_r b (\_ ->
         eq_rec_r x (\_ ->
           eq_rec_r a (\_ -> eq_rec_r s1 (\h1 _ -> iHHstep h1) s) a0) x0) b0
         __ __ __ x1 __;
      _ -> false_rec})) t t' hstep hGU_vars

substituteTCA_preserves_alpha' :: Prelude.String -> Term0 -> Term0 -> Term0
                                  -> Term0 -> (([])
                                  ((,) Prelude.String Prelude.String)) ->
                                  (([]) ((,) Prelude.String Prelude.String))
                                  -> (([])
                                  ((,) Prelude.String Prelude.String)) ->
                                  Alpha -> Alpha -> Coq__UU03b1_CtxTrans ->
                                  Alpha -> Alpha -> Alpha
substituteTCA_preserves_alpha' x t i =
  term_rec (\xi _ _ r1 r2 r ha_X ha_T htrans h_UU03b1_s h_UU03b1_s' ->
    case h_UU03b1_s of {
     Alpha_var x0 y sigma x1 ->
      eq_rec_r r1 (\_ _ ->
        eq_rec_r xi (\h_UU03b1_vs ->
          case h_UU03b1_s' of {
           Alpha_var x2 y0 sigma0 x3 ->
            eq_rec_r r2 (\_ ->
              eq_rec_r xi (\_ h_UU03b1_vs' ->
                let {
                 _evar_0_ = let {
                             _evar_0_ = let {
                                         h_UU03b1_v = alpha_var_trans x0 xi
                                                        y0 r1 r2 r htrans
                                                        h_UU03b1_vs
                                                        h_UU03b1_vs'}
                                        in
                                        let {
                                         b = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                               x x0}
                                        in
                                        case b of {
                                         Prelude.True ->
                                          eq_rec_r x0 (\ha_X0 ->
                                            case ha_X0 of {
                                             Alpha_var x4 y1 sigma1 x5 ->
                                              eq_rec_r r (\_ ->
                                                eq_rec_r x0 (\_ ->
                                                  eq_rec_r x0 (\h2 ->
                                                    eq_rec_r y0 (\_ _ _ _ ->
                                                      eq_rec_r Prelude.True
                                                        ha_T
                                                        (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                          y0 y0)) x0 ha_X0
                                                      h_UU03b1_s h_UU03b1_vs
                                                      h2) y1) x4) sigma1 __
                                                __ x5;
                                             Alpha_lam _ _ _ _ _ _ sigma1
                                              x4 ->
                                              eq_rec_r r (\_ -> false_rec)
                                                sigma1 __ __ x4;
                                             Alpha_app _ _ _ _ _ sigma1 x4
                                              x5 ->
                                              eq_rec_r r (\_ -> false_rec)
                                                sigma1 __ __ x4 x5;
                                             Alpha_builtin r0 _ ->
                                              eq_rec_r r (\_ -> false_rec) r0
                                                __ __}) x ha_X;
                                         Prelude.False ->
                                          case ha_X of {
                                           Alpha_var x4 y1 sigma1 x5 ->
                                            eq_rec_r r (\_ ->
                                              eq_rec_r x (\_ ->
                                                eq_rec_r x (\_ ->
                                                  let {
                                                   _evar_0_ = Alpha_var x0 y0
                                                    r h_UU03b1_v}
                                                  in
                                                  eq_rec_r Prelude.False
                                                    _evar_0_
                                                    (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                      x y0)) y1) x4) sigma1
                                              __ __ x5;
                                           Alpha_lam _ _ _ _ _ _ sigma1 x4 ->
                                            eq_rec_r r (\_ -> false_rec)
                                              sigma1 __ __ x4;
                                           Alpha_app _ _ _ _ _ sigma1 x4
                                            x5 ->
                                            eq_rec_r r (\_ -> false_rec)
                                              sigma1 __ __ x4 x5;
                                           Alpha_builtin r0 _ ->
                                            eq_rec_r r (\_ -> false_rec) r0
                                              __ __}}}
                            in
                            eq_rec_r
                              (case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                      x y0 of {
                                Prelude.True -> t;
                                Prelude.False -> Tmvar y0}) _evar_0_
                              (substituteTCA0 x t (Tmvar y0))}
                in
                eq_rec_r
                  (case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                          x x0 of {
                    Prelude.True -> t;
                    Prelude.False -> Tmvar x0}) _evar_0_
                  (substituteTCA0 x t (Tmvar x0))) x2) sigma0 __ __ x3;
           Alpha_lam _ _ _ _ _ _ sigma0 x2 ->
            eq_rec_r r2 (\_ -> false_rec) sigma0 __ __ x2;
           Alpha_app _ _ _ _ _ sigma0 x2 x3 ->
            eq_rec_r r2 (\_ -> false_rec) sigma0 __ __ x2 x3;
           Alpha_builtin r0 _ -> eq_rec_r r2 (\_ -> false_rec) r0 __ __}) y)
        sigma __ __ x1;
     Alpha_lam _ _ _ _ _ _ sigma x0 ->
      eq_rec_r r1 (\_ _ -> false_rec) sigma __ __ x0;
     Alpha_app _ _ _ _ _ sigma x0 x1 ->
      eq_rec_r r1 (\_ _ -> false_rec) sigma __ __ x0 x1;
     Alpha_builtin r0 _ -> eq_rec_r r1 (\_ _ -> false_rec) r0 __ __})
    (\b xi k bi iHbi _ _ r1 r2 r ha_X ha_T htrans h_UU03b1_s h_UU03b1_s' ->
    case h_UU03b1_s of {
     Alpha_var _ _ sigma x0 -> eq_rec_r r1 (\_ _ -> false_rec) sigma __ __ x0;
     Alpha_lam b0 x0 y a s1 s2 sigma x1 ->
      eq_rec_r r1 (\_ _ ->
        eq_rec_r b (\_ ->
          eq_rec_r xi (\_ ->
            eq_rec_r k (\_ ->
              eq_rec_r bi (\h ->
                eq_rec_r b (\h_UU03b1_s0 ->
                  eq_rec_r k (\h_UU03b1_s1 ->
                    case h_UU03b1_s' of {
                     Alpha_var _ _ sigma0 x2 ->
                      eq_rec_r r2 (\_ -> false_rec) sigma0 __ __ x2;
                     Alpha_lam b1 x2 y0 a0 s3 s4 sigma0 x3 ->
                      eq_rec_r r2 (\_ ->
                        eq_rec_r b (\_ ->
                          eq_rec_r xi (\_ ->
                            eq_rec_r k (\_ ->
                              eq_rec_r bi (\_ h0 ->
                                let {
                                 b2 = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                        x0 x}
                                in
                                case b2 of {
                                 Prelude.True ->
                                  eq_rec_r x (\h_UU03b1_s2 _ ->
                                    let {
                                     _evar_0_ = let {
                                                 _evar_0_ = \_ ->
                                                  let {
                                                   _evar_0_ = alpha_sym
                                                                (substituteTCA0
                                                                  x t (Tmabs
                                                                  b y0 k s4))
                                                                (Tmabs b x k
                                                                s1)
                                                                (sym_alpha_ctx
                                                                  r) r
                                                                (sym_alpha_ctx_left_is_sym
                                                                  r)
                                                                (substituteTCA_vacuous
                                                                  (sym_alpha_ctx
                                                                    r) x t
                                                                  (Tmabs b y0
                                                                  k s4)
                                                                  (Tmabs b x
                                                                  k s1)
                                                                  (alpha_sym
                                                                    (Tmabs b
                                                                    x k s1)
                                                                    (Tmabs b
                                                                    y0 k s4)
                                                                    (sym_alpha_ctx
                                                                    (sym_alpha_ctx
                                                                    r))
                                                                    (sym_alpha_ctx
                                                                    r)
                                                                    (sym_alpha_ctx_left_is_sym
                                                                    (sym_alpha_ctx
                                                                    r))
                                                                    (alpha_sym
                                                                    (Tmabs b
                                                                    y0 k s4)
                                                                    (Tmabs b
                                                                    x k s1)
                                                                    (sym_alpha_ctx
                                                                    r)
                                                                    (sym_alpha_ctx
                                                                    (sym_alpha_ctx
                                                                    r))
                                                                    (sym_alpha_ctx_is_sym
                                                                    (sym_alpha_ctx
                                                                    r))
                                                                    (alpha_sym
                                                                    (Tmabs b
                                                                    x k s1)
                                                                    (Tmabs b
                                                                    y0 k s4)
                                                                    r
                                                                    (sym_alpha_ctx
                                                                    r)
                                                                    (sym_alpha_ctx_is_sym
                                                                    r)
                                                                    (alpha_trans
                                                                    (Tmabs b
                                                                    x k s1)
                                                                    (Tmabs b
                                                                    xi k bi)
                                                                    (Tmabs b
                                                                    y0 k s4)
                                                                    r1 r2 r
                                                                    htrans
                                                                    h_UU03b1_s2
                                                                    h_UU03b1_s')))))}
                                                  in
                                                  eq_rec_r Prelude.True
                                                    _evar_0_
                                                    (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                      x x)}
                                                in
                                                eq_rec_r
                                                  (app ((:) ((,) x t) ([]))
                                                    ([])) _evar_0_ ((:) ((,)
                                                  x t) ([])) __}
                                    in
                                    eq_rec_r
                                      (case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                              x x of {
                                        Prelude.True -> Tmabs b x k s1;
                                        Prelude.False ->
                                         case existsb
                                                (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                  x) (ftv0 t) of {
                                          Prelude.True ->
                                           let {
                                            y' = fresh2 ((:) ((,) x t) ([]))
                                                   s1}
                                           in
                                           let {t' = rename0 x y' s1} in
                                           Tmabs b y' k
                                           (substituteTCA0 x t t');
                                          Prelude.False -> Tmabs b x k
                                           (substituteTCA0 x t s1)}})
                                      _evar_0_
                                      (substituteTCA0 x t (Tmabs b x k s1)))
                                    x0 h_UU03b1_s1 h;
                                 Prelude.False ->
                                  let {
                                   b3 = ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                          y0 x}
                                  in
                                  case b3 of {
                                   Prelude.True ->
                                    eq_rec_r x (\_ h1 ->
                                      let {
                                       _evar_0_ = substituteTCA_vacuous r x t
                                                    (Tmabs b x0 k s1) (Tmabs
                                                    b x k s4) (Alpha_lam b x0
                                                    x k s1 s4 r
                                                    (alpha_trans s1 bi s4
                                                      ((:) ((,) x0 xi) r1)
                                                      ((:) ((,) xi x) r2)
                                                      ((:) ((,) x0 x) r)
                                                      (Alpha_trans_cons x0 xi
                                                      x r1 r2 r htrans) h h1))}
                                      in
                                      eq_rec_r (Tmabs b x k s4) _evar_0_
                                        (substituteTCA0 x t (Tmabs b x k s4)))
                                      y0 h_UU03b1_s' h0;
                                   Prelude.False ->
                                    eq_rec_r
                                      (case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                              x x0 of {
                                        Prelude.True -> Tmabs b x0 k s1;
                                        Prelude.False ->
                                         case existsb
                                                (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                  x0) (ftv0 t) of {
                                          Prelude.True ->
                                           let {
                                            y' = fresh2 ((:) ((,) x t) ([]))
                                                   s1}
                                           in
                                           let {t' = rename0 x0 y' s1} in
                                           Tmabs b y' k
                                           (substituteTCA0 x t t');
                                          Prelude.False -> Tmabs b x0 k
                                           (substituteTCA0 x t s1)}})
                                      (eq_rec_r
                                        (case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                x y0 of {
                                          Prelude.True -> Tmabs b y0 k s4;
                                          Prelude.False ->
                                           case existsb
                                                  (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                    y0) (ftv0 t) of {
                                            Prelude.True ->
                                             let {
                                              y' = fresh2 ((:) ((,) x t)
                                                     ([])) s4}
                                             in
                                             let {t' = rename0 y0 y' s4} in
                                             Tmabs b y' k
                                             (substituteTCA0 x t t');
                                            Prelude.False -> Tmabs b y0 k
                                             (substituteTCA0 x t s4)}})
                                        (let {
                                          _evar_0_ = \_ ->
                                           let {
                                            _evar_0_ = let {
                                                        _evar_0_ = \_ ->
                                                         let {
                                                          _evar_0_ = 
                                                           let {
                                                            b4 = existsb
                                                                   (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    x0)
                                                                   (ftv0 t)}
                                                           in
                                                           case b4 of {
                                                            Prelude.True ->
                                                             let {
                                                              b5 = existsb
                                                                    (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    y0)
                                                                    (ftv0 t)}
                                                             in
                                                             case b5 of {
                                                              Prelude.True ->
                                                               let {
                                                                y' = 
                                                                 fresh2 ((:)
                                                                   ((,) x t)
                                                                   ([])) s1}
                                                               in
                                                               let {
                                                                y'' = 
                                                                 fresh2 ((:)
                                                                   ((,) x t)
                                                                   ([])) s4}
                                                               in
                                                               Alpha_lam b y'
                                                               y'' k
                                                               (substituteTCA0
                                                                 x t
                                                                 (rename0 x0
                                                                   y' s1))
                                                               (substituteTCA0
                                                                 x t
                                                                 (rename0 y0
                                                                   y'' s4)) r
                                                               (iHbi
                                                                 (rename0 x0
                                                                   y' s1)
                                                                 (rename0 y0
                                                                   y'' s4)
                                                                 ((:) ((,) y'
                                                                 xi) r1) ((:)
                                                                 ((,) xi y'')
                                                                 r2) ((:)
                                                                 ((,) y' y'')
                                                                 r)
                                                                 (alpha_extend_fresh
                                                                   y' y'' r
                                                                   (Tmvar x)
                                                                   (Tmvar x)
                                                                   ha_X)
                                                                 (alpha_extend_fresh
                                                                   y' y'' r t
                                                                   t ha_T)
                                                                 (Alpha_trans_cons
                                                                 y' xi y'' r1
                                                                 r2 r htrans)
                                                                 (alpha_trans_rename_left
                                                                   s1 bi y'
                                                                   x0 xi r1
                                                                   ((:) ((,)
                                                                   x t) ([]))
                                                                   h)
                                                                 (alpha_trans_rename_right
                                                                   bi s4 y''
                                                                   y0 xi r2
                                                                   ((:) ((,)
                                                                   x t) ([]))
                                                                   h0));
                                                              Prelude.False ->
                                                               let {
                                                                y' = 
                                                                 fresh2 ((:)
                                                                   ((,) x t)
                                                                   ([])) s1}
                                                               in
                                                               Alpha_lam b y'
                                                               y0 k
                                                               (substituteTCA0
                                                                 x t
                                                                 (rename0 x0
                                                                   y' s1))
                                                               (substituteTCA0
                                                                 x t s4) r
                                                               (iHbi
                                                                 (rename0 x0
                                                                   y' s1) s4
                                                                 ((:) ((,) y'
                                                                 xi) r1) ((:)
                                                                 ((,) xi y0)
                                                                 r2) ((:)
                                                                 ((,) y' y0)
                                                                 r)
                                                                 (alpha_extend_fresh
                                                                   y' y0 r
                                                                   (Tmvar x)
                                                                   (Tmvar x)
                                                                   ha_X)
                                                                 (alpha_extend_fresh
                                                                   y' y0 r t
                                                                   t ha_T)
                                                                 (Alpha_trans_cons
                                                                 y' xi y0 r1
                                                                 r2 r htrans)
                                                                 (alpha_trans_rename_left
                                                                   s1 bi y'
                                                                   x0 xi r1
                                                                   ((:) ((,)
                                                                   x t) ([]))
                                                                   h) h0)};
                                                            Prelude.False ->
                                                             let {
                                                              b5 = existsb
                                                                    (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    y0)
                                                                    (ftv0 t)}
                                                             in
                                                             case b5 of {
                                                              Prelude.True ->
                                                               let {
                                                                y' = 
                                                                 fresh2 ((:)
                                                                   ((,) x t)
                                                                   ([])) s4}
                                                               in
                                                               Alpha_lam b x0
                                                               y' k
                                                               (substituteTCA0
                                                                 x t s1)
                                                               (substituteTCA0
                                                                 x t
                                                                 (rename0 y0
                                                                   y' s4)) r
                                                               (iHbi s1
                                                                 (rename0 y0
                                                                   y' s4)
                                                                 ((:) ((,) x0
                                                                 xi) r1) ((:)
                                                                 ((,) xi y')
                                                                 r2) ((:)
                                                                 ((,) x0 y')
                                                                 r)
                                                                 (alpha_extend_fresh
                                                                   x0 y' r
                                                                   (Tmvar x)
                                                                   (Tmvar x)
                                                                   ha_X)
                                                                 (alpha_extend_fresh
                                                                   x0 y' r t
                                                                   t ha_T)
                                                                 (Alpha_trans_cons
                                                                 x0 xi y' r1
                                                                 r2 r htrans)
                                                                 h
                                                                 (alpha_trans_rename_right
                                                                   bi s4 y'
                                                                   y0 xi r2
                                                                   ((:) ((,)
                                                                   x t) ([]))
                                                                   h0));
                                                              Prelude.False ->
                                                               Alpha_lam b x0
                                                               y0 k
                                                               (substituteTCA0
                                                                 x t s1)
                                                               (substituteTCA0
                                                                 x t s4) r
                                                               (iHbi s1 s4
                                                                 ((:) ((,) x0
                                                                 xi) r1) ((:)
                                                                 ((,) xi y0)
                                                                 r2) ((:)
                                                                 ((,) x0 y0)
                                                                 r)
                                                                 (alpha_extend_fresh
                                                                   x0 y0 r
                                                                   (Tmvar x)
                                                                   (Tmvar x)
                                                                   ha_X)
                                                                 (alpha_extend_fresh
                                                                   x0 y0 r t
                                                                   t ha_T)
                                                                 (Alpha_trans_cons
                                                                 x0 xi y0 r1
                                                                 r2 r htrans)
                                                                 h h0)}}}
                                                         in
                                                         eq_rec_r
                                                           Prelude.False
                                                           _evar_0_
                                                           (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                             x y0)}
                                                       in
                                                       eq_rec_r
                                                         (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                           x y0) _evar_0_
                                                         (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                           y0 x) __}
                                           in
                                           eq_rec_r Prelude.False _evar_0_
                                             (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                               x x0)}
                                         in
                                         eq_rec_r
                                           (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                             x x0) _evar_0_
                                           (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                             x0 x) __)
                                        (substituteTCA0 x t (Tmabs b y0 k
                                          s4)))
                                      (substituteTCA0 x t (Tmabs b x0 k s1))}})
                                s3) a0) x2) b1 __ __ __) sigma0 __ __ x3;
                     Alpha_app _ _ _ _ _ sigma0 x2 x3 ->
                      eq_rec_r r2 (\_ -> false_rec) sigma0 __ __ x2 x3;
                     Alpha_builtin r0 _ ->
                      eq_rec_r r2 (\_ -> false_rec) r0 __ __}) a h_UU03b1_s0)
                  b0 h_UU03b1_s) s2) a) y) b0 __ __ __) sigma __ __ x1;
     Alpha_app _ _ _ _ _ sigma x0 x1 ->
      eq_rec_r r1 (\_ _ -> false_rec) sigma __ __ x0 x1;
     Alpha_builtin r0 _ -> eq_rec_r r1 (\_ _ -> false_rec) r0 __ __})
    (\b i1 iHi1 i2 iHi2 _ _ r1 r2 r ha_X ha_T htrans h_UU03b1_s h_UU03b1_s' ->
    case h_UU03b1_s of {
     Alpha_var _ _ sigma x0 -> eq_rec_r r1 (\_ _ -> false_rec) sigma __ __ x0;
     Alpha_lam _ _ _ _ _ _ sigma x0 ->
      eq_rec_r r1 (\_ _ -> false_rec) sigma __ __ x0;
     Alpha_app b0 s1 s2 t1 t2 sigma x0 x1 ->
      eq_rec_r r1 (\_ _ ->
        eq_rec_r b (\_ ->
          eq_rec_r i1 (\_ ->
            eq_rec_r i2 (\h_UU03b1_s2 h ->
              eq_rec_r b (\_ ->
                case h_UU03b1_s' of {
                 Alpha_var _ _ sigma0 x2 ->
                  eq_rec_r r2 (\_ -> false_rec) sigma0 __ __ x2;
                 Alpha_lam _ _ _ _ _ _ sigma0 x2 ->
                  eq_rec_r r2 (\_ -> false_rec) sigma0 __ __ x2;
                 Alpha_app b1 s3 s4 t3 t4 sigma0 x2 x3 ->
                  eq_rec_r r2 (\_ ->
                    eq_rec_r b (\_ ->
                      eq_rec_r i1 (\_ ->
                        eq_rec_r i2 (\_ h_UU03b1_s2' h0 ->
                          eq_rec_r (Tmbin b (substituteTCA0 x t s1)
                            (substituteTCA0 x t t1))
                            (eq_rec_r (Tmbin b (substituteTCA0 x t s4)
                              (substituteTCA0 x t t4)) (Alpha_app b
                              (substituteTCA0 x t s1) (substituteTCA0 x t s4)
                              (substituteTCA0 x t t1) (substituteTCA0 x t t4)
                              r
                              (iHi1 s1 s4 r1 r2 r ha_X ha_T htrans
                                h_UU03b1_s2 h_UU03b1_s2')
                              (iHi2 t1 t4 r1 r2 r ha_X ha_T htrans h h0))
                              (substituteTCA0 x t (Tmbin b s4 t4)))
                            (substituteTCA0 x t (Tmbin b s1 t1))) t3) s3) b1
                      __ __) sigma0 __ __ x2 x3;
                 Alpha_builtin r0 _ -> eq_rec_r r2 (\_ -> false_rec) r0 __ __})
                b0 h_UU03b1_s) t2) s2) b0 __ __) sigma __ __ x0 x1;
     Alpha_builtin r0 _ -> eq_rec_r r1 (\_ _ -> false_rec) r0 __ __})
    (\d _ _ r1 r2 r _ _ _ h_UU03b1_s h_UU03b1_s' ->
    case h_UU03b1_s of {
     Alpha_var _ _ sigma x0 -> eq_rec_r r1 (\_ _ -> false_rec) sigma __ __ x0;
     Alpha_lam _ _ _ _ _ _ sigma x0 ->
      eq_rec_r r1 (\_ _ -> false_rec) sigma __ __ x0;
     Alpha_app _ _ _ _ _ sigma x0 x1 ->
      eq_rec_r r1 (\_ _ -> false_rec) sigma __ __ x0 x1;
     Alpha_builtin r0 d0 ->
      eq_rec_r r1 (\_ _ ->
        eq_rec_r d
          (eq_rec_r d (\_ ->
            case h_UU03b1_s' of {
             Alpha_var _ _ sigma x0 ->
              eq_rec_r r2 (\_ -> false_rec) sigma __ __ x0;
             Alpha_lam _ _ _ _ _ _ sigma x0 ->
              eq_rec_r r2 (\_ -> false_rec) sigma __ __ x0;
             Alpha_app _ _ _ _ _ sigma x0 x1 ->
              eq_rec_r r2 (\_ -> false_rec) sigma __ __ x0 x1;
             Alpha_builtin r3 d1 ->
              eq_rec_r r2 (\_ ->
                eq_rec_r d (\_ ->
                  eq_rec_r (Tmbuiltin d) (Alpha_builtin r d)
                    (substituteTCA0 x t (Tmbuiltin d))) d1) r3 __ __}) d0
            h_UU03b1_s) d0) r0 __ __}) i

substituteTCA_preserves_alpha :: Term0 -> Term0 -> (([])
                                 ((,) Prelude.String Prelude.String)) ->
                                 Prelude.String -> Term0 -> Alpha -> Alpha ->
                                 Alpha -> Alpha
substituteTCA_preserves_alpha s s' ren x u x0 x1 x2 =
  substituteTCA_preserves_alpha' x u s s s' (app ([]) (ctx_id_left ren)) ren
    ren x0 x1 (id_left_trans ren)
    (alpha_extend_ids_right s s ([]) (ctx_id_left ren)
      (ctx_id_left_is_id ren) (alpha_refl s ([]) Alpha_refl_nil)) x2

alpha_substituteTCA_sub :: Prelude.String -> Term0 -> Term0 -> SigT Term0
                           ((,) ((,) Alpha Alpha) NC)
alpha_substituteTCA_sub x u t =
  ExistT (to_GU' x u t) ((,) ((,) (to_GU'__alpha x u t)
    (alpha_trans (substituteTCA0 x u t) (substituteTCA0 x u (to_GU' x u t))
      (sub x u (to_GU' x u t)) ([]) ([]) ([]) Alpha_trans_nil
      (substituteTCA_preserves_alpha t (to_GU' x u t) ([]) x u
        (alpha_refl (Tmvar x) ([]) Alpha_refl_nil)
        (alpha_refl u ([]) Alpha_refl_nil) (to_GU'__alpha x u t))
      (eq_rec_r (sub x u (to_GU' x u t))
        (alpha_refl (sub x u (to_GU' x u t)) ([]) Alpha_refl_nil)
        (substituteTCA0 x u (to_GU' x u t))))) (to_GU'__NC x u t))

step_nd_preserves_alpha :: (([]) ((,) Prelude.String Prelude.String)) ->
                           Term0 -> Term0 -> Term0 -> Alpha -> Step_nd ->
                           SigT Term0 ((,) Step_nd Alpha)
step_nd_preserves_alpha ren s t s' halpha hstep =
  step_nd_rec (\x a s0 t0 ren0 _ halpha0 ->
    case halpha0 of {
     Alpha_var _ _ sigma x0 -> eq_rec_r ren0 (\_ -> false_rec) sigma __ __ x0;
     Alpha_lam _ _ _ _ _ _ sigma x0 ->
      eq_rec_r ren0 (\_ -> false_rec) sigma __ __ x0;
     Alpha_app b s1 _ t1 t2 sigma x0 x1 ->
      eq_rec_r ren0 (\_ ->
        eq_rec_r App (\_ ->
          eq_rec_r (Tmabs Lam x a s0) (\_ ->
            eq_rec_r t0 (\_ h4 h5 ->
              case h4 of {
               Alpha_var _ _ sigma0 x2 ->
                eq_rec_r ren0 (\_ -> false_rec) sigma0 __ __ x2;
               Alpha_lam b0 x2 y a0 s2 s3 sigma0 x3 ->
                eq_rec_r ren0 (\_ ->
                  eq_rec_r Lam (\_ ->
                    eq_rec_r x (\_ ->
                      eq_rec_r a (\_ ->
                        eq_rec_r s0 (\_ h7 ->
                          let {s4 = alpha_substituteTCA_sub x t0 s0} in
                          case s4 of {
                           ExistT x4 p ->
                            case p of {
                             (,) p0 n ->
                              case p0 of {
                               (,) a1 a2 -> ExistT (substituteTCA0 y t2 s3)
                                ((,) (Step_beta_nd y a s3 t2)
                                (alpha_trans (substituteTCA0 x t0 s0)
                                  (sub x t0 x4) (substituteTCA0 y t2 s3)
                                  (ctx_id_left ren0) ren0 ren0
                                  (id_left_trans ren0)
                                  (alpha_extend_ids (ctx_id_left ren0)
                                    (substituteTCA0 x t0 s0) (sub x t0 x4)
                                    (ctx_id_left_is_id ren0) a2)
                                  (let {s5 = alpha_substituteTCA_sub y t2 s3}
                                   in
                                   case s5 of {
                                    ExistT x5 p1 ->
                                     case p1 of {
                                      (,) p2 n0 ->
                                       case p2 of {
                                        (,) a3 a4 ->
                                         alpha_trans (sub x t0 x4)
                                           (sub y t2 x5)
                                           (substituteTCA0 y t2 s3) ren0
                                           (ctx_id_right ren0) ren0
                                           (id_right_trans ren0)
                                           (alpha_rename_binder_stronger x y
                                             x4 t0 t2 ren0 x5 ((:) ((,) x y)
                                             ren0)
                                             (alpha_trans x4 s0 x5
                                               (ctx_id_left ((:) ((,) x y)
                                                 ren0)) ((:) ((,) x y) ren0)
                                               ((:) ((,) x y) ren0)
                                               (id_left_trans ((:) ((,) x y)
                                                 ren0))
                                               (alpha_extend_ids
                                                 (ctx_id_left ((:) ((,) x y)
                                                   ren0)) x4 s0
                                                 (ctx_id_left_is_id ((:) ((,)
                                                   x y) ren0))
                                                 (alpha_extend_ids ([]) x4 s0
                                                   Id_ctx_nil
                                                   (alpha_extend_ids ([]) x4
                                                     s0 Id_ctx_nil
                                                     (alpha_sym s0 x4
                                                       (sym_alpha_ctx ([]))
                                                       ([])
                                                       (sym_alpha_ctx_left_is_sym
                                                         ([])) a1))))
                                               (alpha_sym x5 s0
                                                 (sym_alpha_ctx ((:) ((,) x
                                                   y) ren0)) ((:) ((,) x y)
                                                 ren0)
                                                 (sym_alpha_ctx_left_is_sym
                                                   ((:) ((,) x y) ren0))
                                                 (alpha_sym s0 x5 ((:) ((,) x
                                                   y) ren0)
                                                   (sym_alpha_ctx ((:) ((,) x
                                                     y) ren0))
                                                   (sym_alpha_ctx_is_sym ((:)
                                                     ((,) x y) ren0))
                                                   (alpha_trans s0 s3 x5 ((:)
                                                     ((,) x y) ren0)
                                                     (ctx_id_right ((:) ((,)
                                                       x y) ren0)) ((:) ((,)
                                                     x y) ren0)
                                                     (id_right_trans ((:)
                                                       ((,) x y) ren0)) h7
                                                     (alpha_extend_ids
                                                       (ctx_id_right ((:)
                                                         ((,) x y) ren0)) s3
                                                       x5
                                                       (ctx_id_right_is_id
                                                         ((:) ((,) x y)
                                                         ren0)) a3))))) h5
                                             StarR n n0)
                                           (alpha_extend_ids
                                             (ctx_id_right ren0)
                                             (sub y t2 x5)
                                             (substituteTCA0 y t2 s3)
                                             (ctx_id_right_is_id ren0)
                                             (alpha_extend_ids ([])
                                               (sub y t2 x5)
                                               (substituteTCA0 y t2 s3)
                                               Id_ctx_nil
                                               (alpha_extend_ids ([])
                                                 (sub y t2 x5)
                                                 (substituteTCA0 y t2 s3)
                                                 Id_ctx_nil
                                                 (alpha_sym
                                                   (substituteTCA0 y t2 s3)
                                                   (sub y t2 x5)
                                                   (sym_alpha_ctx ([])) ([])
                                                   (sym_alpha_ctx_left_is_sym
                                                     ([])) a4))))}}})))}}})
                          s2) a0) x2) b0 __ __ __) sigma0 __ __ x3;
               Alpha_app _ _ _ _ _ sigma0 x2 x3 ->
                eq_rec_r ren0 (\_ -> false_rec) sigma0 __ __ x2 x3;
               Alpha_builtin r _ -> eq_rec_r ren0 (\_ -> false_rec) r __ __})
              t1) s1) b __ __) sigma __ __ x0 x1;
     Alpha_builtin r _ -> eq_rec_r ren0 (\_ -> false_rec) r __ __})
    (\b s1 s2 t0 _ iHHstep ren0 _ halpha0 ->
    case halpha0 of {
     Alpha_var _ _ sigma x -> eq_rec_r ren0 (\_ -> false_rec) sigma __ __ x;
     Alpha_lam _ _ _ _ _ _ sigma x ->
      eq_rec_r ren0 (\_ -> false_rec) sigma __ __ x;
     Alpha_app b0 s3 s4 t1 t2 sigma x x0 ->
      eq_rec_r ren0 (\_ ->
        eq_rec_r b (\_ ->
          eq_rec_r s1 (\_ ->
            eq_rec_r t0 (\_ h4 h5 ->
              let {s0 = iHHstep ren0 s4 h4} in
              case s0 of {
               ExistT x1 p ->
                case p of {
                 (,) s5 a -> ExistT (Tmbin b x1 t2) ((,) (Step_appL_nd b s4
                  x1 t2 s5) (Alpha_app b s2 x1 t0 t2 ren0 a h5))}}) t1) s3)
          b0 __ __) sigma __ __ x x0;
     Alpha_builtin r _ -> eq_rec_r ren0 (\_ -> false_rec) r __ __})
    (\b s0 t1 t2 _ iHHstep ren0 _ halpha0 ->
    case halpha0 of {
     Alpha_var _ _ sigma x -> eq_rec_r ren0 (\_ -> false_rec) sigma __ __ x;
     Alpha_lam _ _ _ _ _ _ sigma x ->
      eq_rec_r ren0 (\_ -> false_rec) sigma __ __ x;
     Alpha_app b0 s1 s2 t3 t4 sigma x x0 ->
      eq_rec_r ren0 (\_ ->
        eq_rec_r b (\_ ->
          eq_rec_r s0 (\_ ->
            eq_rec_r t1 (\_ h4 h5 ->
              let {s3 = iHHstep ren0 t4 h5} in
              case s3 of {
               ExistT x1 p ->
                case p of {
                 (,) s4 a -> ExistT (Tmbin b s2 x1) ((,) (Step_appR_nd b s2
                  t4 x1 s4) (Alpha_app b s0 s2 t2 x1 ren0 h4 a))}}) t3) s1)
          b0 __ __) sigma __ __ x x0;
     Alpha_builtin r _ -> eq_rec_r ren0 (\_ -> false_rec) r __ __})
    (\b x a s1 s2 _ iHHstep ren0 _ halpha0 ->
    case halpha0 of {
     Alpha_var _ _ sigma x0 -> eq_rec_r ren0 (\_ -> false_rec) sigma __ __ x0;
     Alpha_lam b0 x0 y a0 s3 s4 sigma x1 ->
      eq_rec_r ren0 (\_ ->
        eq_rec_r b (\_ ->
          eq_rec_r x (\_ ->
            eq_rec_r a (\_ ->
              eq_rec_r s1 (\_ h5 ->
                let {s0 = iHHstep ((:) ((,) x y) ren0) s4 h5} in
                case s0 of {
                 ExistT x2 p ->
                  case p of {
                   (,) s5 a1 -> ExistT (Tmabs b y a x2) ((,) (Step_abs_nd b y
                    a s4 x2 s5) (Alpha_lam b x y a s2 x2 ren0 a1))}}) s3) a0)
            x0) b0 __ __ __) sigma __ __ x1;
     Alpha_app _ _ _ _ _ sigma x0 x1 ->
      eq_rec_r ren0 (\_ -> false_rec) sigma __ __ x0 x1;
     Alpha_builtin r _ -> eq_rec_r ren0 (\_ -> false_rec) r __ __}) s s'
    hstep ren t halpha

step_nd_implies_step_gu :: Term0 -> Term0 -> Step_nd -> SigT Term0
                           ((,) Step_gu Alpha)
step_nd_implies_step_gu t t' x =
  let {s = step_nd_preserves_alpha ([]) t (to_GU t) t' (to_GU__alpha t) x} in
  case s of {
   ExistT x0 p ->
    case p of {
     (,) s0 a -> ExistT x0 ((,)
      (let {
        hstep_GU' = gU_step_d_implies_step_na (to_GU t) x0 (to_GU__GU t) s0}
       in
       Step_gu_intro t (to_GU t) x0 (to_GU__alpha t) (to_GU__GU t) hstep_GU')
      a)}}

_UU03b1__preserves_sn_nd :: Term0 -> Term0 -> Alpha -> (Sn Term0 Step_nd) ->
                            Sn Term0 Step_nd
_UU03b1__preserves_sn_nd s s' h_UU03b1_ hsn =
  sn_rect (\x _ x0 s'0 h_UU03b1_0 -> SNI (\y1 hstep ->
    let {
     s0 = step_nd_preserves_alpha ([]) s'0 x y1
            (alpha_extend_ids ([]) s'0 x Id_ctx_nil
              (alpha_extend_ids ([]) s'0 x Id_ctx_nil
                (alpha_extend_ids ([]) s'0 x Id_ctx_nil
                  (alpha_sym x s'0 (sym_alpha_ctx ([])) ([])
                    (sym_alpha_ctx_left_is_sym ([])) h_UU03b1_0)))) hstep}
    in
    case s0 of {
     ExistT x1 p ->
      case p of {
       (,) s1 a ->
        x0 x1 s1 y1
          (alpha_extend_ids ([]) x1 y1 Id_ctx_nil
            (alpha_extend_ids ([]) x1 y1 Id_ctx_nil
              (alpha_sym y1 x1 (sym_alpha_ctx ([])) ([])
                (sym_alpha_ctx_left_is_sym ([])) a)))}})) s hsn s' h_UU03b1_

sN_na_to_SN_nd :: Term0 -> (Sn Term0 Step_gu) -> Sn Term0 Step_nd
sN_na_to_SN_nd t hsn_nd =
  SNI (\t' hstep ->
    sn_rect (\x _ x0 t0 hstep_d ->
      let {s0 = step_nd_implies_step_gu x t0 hstep_d} in
      case s0 of {
       ExistT x1 p ->
        case p of {
         (,) s a ->
          let {x2 = x0 x1 s} in
          _UU03b1__preserves_sn_nd x1 t0
            (alpha_extend_ids ([]) x1 t0 Id_ctx_nil
              (alpha_extend_ids ([]) x1 t0 Id_ctx_nil
                (alpha_extend_ids ([]) x1 t0 Id_ctx_nil
                  (alpha_sym t0 x1 (sym_alpha_ctx ([])) ([])
                    (sym_alpha_ctx_left_is_sym ([])) a)))) (SNI x2)}}) t
      hsn_nd t' hstep)

strong_normalization_nd :: (([]) ((,) BinderTyname Kind)) -> Term0 -> Kind ->
                           Has_kind -> Sn Term0 Step_nd
strong_normalization_nd _UU0394_ s t x =
  let {h = strong_normalization_gu _UU0394_ s t x} in sN_na_to_SN_nd s h

f :: Ty -> Term0
f t =
  case t of {
   Ty_Var x -> Tmvar x;
   Ty_Fun t1 t2 -> Tmbin Fun (f t1) (f t2);
   Ty_IFix f1 t1 -> Tmbin IFix (f f1) (f t1);
   Ty_Forall x a t0 -> Tmabs ForAll x a (f t0);
   Ty_Builtin d -> Tmbuiltin d;
   Ty_Lam x a t0 -> Tmabs Lam x a (f t0);
   Ty_App t1 t2 -> Tmbin App (f t1) (f t2);
   Ty_SOP tss ->
    fold_right (\ts acc ->
      fold_right (\t0 acc2 -> Tmbin Fun (f t0) acc2) acc ts) (Tmbuiltin
      DefaultUniInteger) tss}

f_preserves_step :: Ty -> Ty -> Step -> Step_nd
f_preserves_step s s' h =
  step_rec (\x k s0 t _ _ ->
    eq_rec_r (substituteTCA0 x (f t) (f s0)) (Step_beta_nd x k (f s0) 
      (f t)) (f (substituteTCA x t s0))) (\s1 s2 t _ iHstep -> Step_appL_nd
    App (f s1) (f s2) (f t) iHstep) (\s0 t1 t2 _ _ iHstep -> Step_appR_nd App
    (f s0) (f t1) (f t2) iHstep) (\s1 s2 t _ iHstep -> Step_appL_nd Fun
    (f s1) (f s2) (f t) iHstep) (\s0 t1 t2 _ _ iHstep -> Step_appR_nd Fun
    (f s0) (f t1) (f t2) iHstep) (\bX k s1 s2 _ iHstep -> Step_abs_nd ForAll
    bX k (f s1) (f s2) iHstep) (\bX k t1 t2 _ iHstep -> Step_abs_nd Lam bX k
    (f t1) (f t2) iHstep) (\f1 f2 t _ iHstep -> Step_appL_nd IFix (f f1)
    (f f2) (f t) iHstep) (\f0 t1 t2 _ _ iHstep -> Step_appR_nd IFix (f f0)
    (f t1) (f t2) iHstep)
    (\tss_normal tss_sub_normal tss_sub1 tss_sub2 tss_sub_remainder tss_remainder f0 f1 _ iHstep ->
    forallSet2_rec
      (forallSet_rec (Step_appL_nd Fun (f tss_sub1) (f tss_sub2)
        (fold_right (\t acc2 -> Tmbin Fun (f t) acc2)
          (fold_right (\ts acc ->
            fold_right (\t acc2 -> Tmbin Fun (f t) acc2) acc ts) (Tmbuiltin
            DefaultUniInteger) tss_remainder) tss_sub_remainder) iHstep)
        (\x xs _ _ iHf1 -> Step_appR_nd Fun (f x)
        (fold_right (\t acc2 -> Tmbin Fun (f t) acc2)
          (fold_right (\ts acc ->
            fold_right (\t acc2 -> Tmbin Fun (f t) acc2) acc ts) (Tmbuiltin
            DefaultUniInteger) tss_remainder)
          (app xs ((:) tss_sub1 tss_sub_remainder)))
        (fold_right (\t acc2 -> Tmbin Fun (f t) acc2)
          (fold_right (\ts acc ->
            fold_right (\t acc2 -> Tmbin Fun (f t) acc2) acc ts) (Tmbuiltin
            DefaultUniInteger) tss_remainder)
          (app xs ((:) tss_sub2 tss_sub_remainder))) iHf1) tss_sub_normal f1)
      (\x xs f2 _ iHf0 ->
      list_rec (\_ -> iHf0) (\a x0 iHx f3 -> Step_appR_nd Fun (f a)
        (fold_right (\t acc2 -> Tmbin Fun (f t) acc2)
          (fold_right (\ts acc ->
            fold_right (\t acc2 -> Tmbin Fun (f t) acc2) acc ts) (Tmbuiltin
            DefaultUniInteger)
            (app xs ((:)
              (app tss_sub_normal ((:) tss_sub1 tss_sub_remainder))
              tss_remainder))) x0)
        (fold_right (\t acc2 -> Tmbin Fun (f t) acc2)
          (fold_right (\ts acc ->
            fold_right (\t acc2 -> Tmbin Fun (f t) acc2) acc ts) (Tmbuiltin
            DefaultUniInteger)
            (app xs ((:)
              (app tss_sub_normal ((:) tss_sub2 tss_sub_remainder))
              tss_remainder))) x0)
        (iHx
          (case f3 of {
            ForallS_nil -> false_rec;
            ForallS_cons x1 xs0 _ x2 ->
             eq_rec_r a (\_ -> eq_rec_r x0 (\_ h3 -> h3) xs0) x1 __ __ x2})))
        x f2) tss_normal f0) s s' h

f_preserves_kind :: (([]) ((,) BinderTyname Kind)) -> Ty -> Kind -> Has_kind
f_preserves_kind _UU0394_ s k =
  let {h = prop_to_type _UU0394_ s k} in
  has_kind_set__ind (\_UU0394_0 x k0 _ -> K_Var _UU0394_0 x k0)
    (\_UU0394_0 t1 t2 iHhas_kind_set iHhas_kind_set0 -> K_Fun _UU0394_0
    (let {
      f0 t =
        case t of {
         Ty_Var x -> Tmvar x;
         Ty_Fun t3 t4 -> Tmbin Fun (f0 t3) (f0 t4);
         Ty_IFix f1 t3 -> Tmbin IFix (f0 f1) (f0 t3);
         Ty_Forall x a t0 -> Tmabs ForAll x a (f0 t0);
         Ty_Builtin d -> Tmbuiltin d;
         Ty_Lam x a t0 -> Tmabs Lam x a (f0 t0);
         Ty_App t3 t4 -> Tmbin App (f0 t3) (f0 t4);
         Ty_SOP tss ->
          fold_right (\ts acc ->
            fold_right (\t0 acc2 -> Tmbin Fun (f0 t0) acc2) acc ts)
            (Tmbuiltin DefaultUniInteger) tss}}
     in f0 t1)
    (let {
      f0 t =
        case t of {
         Ty_Var x -> Tmvar x;
         Ty_Fun t3 t4 -> Tmbin Fun (f0 t3) (f0 t4);
         Ty_IFix f1 t3 -> Tmbin IFix (f0 f1) (f0 t3);
         Ty_Forall x a t0 -> Tmabs ForAll x a (f0 t0);
         Ty_Builtin d -> Tmbuiltin d;
         Ty_Lam x a t0 -> Tmabs Lam x a (f0 t0);
         Ty_App t3 t4 -> Tmbin App (f0 t3) (f0 t4);
         Ty_SOP tss ->
          fold_right (\ts acc ->
            fold_right (\t0 acc2 -> Tmbin Fun (f0 t0) acc2) acc ts)
            (Tmbuiltin DefaultUniInteger) tss}}
     in f0 t2) iHhas_kind_set iHhas_kind_set0)
    (\_UU0394_0 f0 t k0 iHhas_kind_set iHhas_kind_set0 -> K_IFix _UU0394_0
    (let {
      f1 t0 =
        case t0 of {
         Ty_Var x -> Tmvar x;
         Ty_Fun t1 t2 -> Tmbin Fun (f1 t1) (f1 t2);
         Ty_IFix f2 t1 -> Tmbin IFix (f1 f2) (f1 t1);
         Ty_Forall x a t1 -> Tmabs ForAll x a (f1 t1);
         Ty_Builtin d -> Tmbuiltin d;
         Ty_Lam x a t1 -> Tmabs Lam x a (f1 t1);
         Ty_App t1 t2 -> Tmbin App (f1 t1) (f1 t2);
         Ty_SOP tss ->
          fold_right (\ts acc ->
            fold_right (\t1 acc2 -> Tmbin Fun (f1 t1) acc2) acc ts)
            (Tmbuiltin DefaultUniInteger) tss}}
     in f1 f0)
    (let {
      f1 t0 =
        case t0 of {
         Ty_Var x -> Tmvar x;
         Ty_Fun t1 t2 -> Tmbin Fun (f1 t1) (f1 t2);
         Ty_IFix f2 t1 -> Tmbin IFix (f1 f2) (f1 t1);
         Ty_Forall x a t1 -> Tmabs ForAll x a (f1 t1);
         Ty_Builtin d -> Tmbuiltin d;
         Ty_Lam x a t1 -> Tmabs Lam x a (f1 t1);
         Ty_App t1 t2 -> Tmbin App (f1 t1) (f1 t2);
         Ty_SOP tss ->
          fold_right (\ts acc ->
            fold_right (\t1 acc2 -> Tmbin Fun (f1 t1) acc2) acc ts)
            (Tmbuiltin DefaultUniInteger) tss}}
     in f1 t) k0 iHhas_kind_set iHhas_kind_set0)
    (\_UU0394_0 x k0 t iHhas_kind_set -> K_Forall _UU0394_0 x k0
    (let {
      f0 t0 =
        case t0 of {
         Ty_Var x0 -> Tmvar x0;
         Ty_Fun t1 t2 -> Tmbin Fun (f0 t1) (f0 t2);
         Ty_IFix f1 t1 -> Tmbin IFix (f0 f1) (f0 t1);
         Ty_Forall x0 a t1 -> Tmabs ForAll x0 a (f0 t1);
         Ty_Builtin d -> Tmbuiltin d;
         Ty_Lam x0 a t1 -> Tmabs Lam x0 a (f0 t1);
         Ty_App t1 t2 -> Tmbin App (f0 t1) (f0 t2);
         Ty_SOP tss ->
          fold_right (\ts acc ->
            fold_right (\t1 acc2 -> Tmbin Fun (f0 t1) acc2) acc ts)
            (Tmbuiltin DefaultUniInteger) tss}}
     in f0 t) iHhas_kind_set) (\_UU0394_0 t _ -> K_Builtin _UU0394_0 t)
    (\_UU0394_0 x k1 t k2 iHhas_kind_set -> K_Lam _UU0394_0 x k1
    (let {
      f0 t0 =
        case t0 of {
         Ty_Var x0 -> Tmvar x0;
         Ty_Fun t1 t2 -> Tmbin Fun (f0 t1) (f0 t2);
         Ty_IFix f1 t1 -> Tmbin IFix (f0 f1) (f0 t1);
         Ty_Forall x0 a t1 -> Tmabs ForAll x0 a (f0 t1);
         Ty_Builtin d -> Tmbuiltin d;
         Ty_Lam x0 a t1 -> Tmabs Lam x0 a (f0 t1);
         Ty_App t1 t2 -> Tmbin App (f0 t1) (f0 t2);
         Ty_SOP tss ->
          fold_right (\ts acc ->
            fold_right (\t1 acc2 -> Tmbin Fun (f0 t1) acc2) acc ts)
            (Tmbuiltin DefaultUniInteger) tss}}
     in f0 t) k2 iHhas_kind_set)
    (\_UU0394_0 t1 t2 k1 k2 iHhas_kind_set iHhas_kind_set0 -> K_App _UU0394_0
    (let {
      f0 t =
        case t of {
         Ty_Var x -> Tmvar x;
         Ty_Fun t3 t4 -> Tmbin Fun (f0 t3) (f0 t4);
         Ty_IFix f1 t3 -> Tmbin IFix (f0 f1) (f0 t3);
         Ty_Forall x a t0 -> Tmabs ForAll x a (f0 t0);
         Ty_Builtin d -> Tmbuiltin d;
         Ty_Lam x a t0 -> Tmabs Lam x a (f0 t0);
         Ty_App t3 t4 -> Tmbin App (f0 t3) (f0 t4);
         Ty_SOP tss ->
          fold_right (\ts acc ->
            fold_right (\t0 acc2 -> Tmbin Fun (f0 t0) acc2) acc ts)
            (Tmbuiltin DefaultUniInteger) tss}}
     in f0 t1)
    (let {
      f0 t =
        case t of {
         Ty_Var x -> Tmvar x;
         Ty_Fun t3 t4 -> Tmbin Fun (f0 t3) (f0 t4);
         Ty_IFix f1 t3 -> Tmbin IFix (f0 f1) (f0 t3);
         Ty_Forall x a t0 -> Tmabs ForAll x a (f0 t0);
         Ty_Builtin d -> Tmbuiltin d;
         Ty_Lam x a t0 -> Tmabs Lam x a (f0 t0);
         Ty_App t3 t4 -> Tmbin App (f0 t3) (f0 t4);
         Ty_SOP tss ->
          fold_right (\ts acc ->
            fold_right (\t0 acc2 -> Tmbin Fun (f0 t0) acc2) acc ts)
            (Tmbuiltin DefaultUniInteger) tss}}
     in f0 t2) k1 k2 iHhas_kind_set iHhas_kind_set0) (\_UU0394_0 tss h0 ->
    list_rec (\_ -> K_Builtin _UU0394_0 DefaultUniInteger)
      (\a tss0 iHTss h1 ->
      list_rec (\h2 ->
        iHTss
          (case h2 of {
            ForallT_nil -> false_rec;
            ForallT_cons x l x0 x1 ->
             eq_rec_r ([]) (\_ -> eq_rec_r tss0 (\_ h3 -> h3) l) x __ x0 x1}))
        (\a0 a1 iHa h2 -> K_Fun _UU0394_0 (f a0)
        (let {
          fold_right0 l =
            case l of {
             ([]) ->
              fold_right (\ts acc ->
                fold_right (\t acc2 -> Tmbin Fun (f t) acc2) acc ts)
                (Tmbuiltin DefaultUniInteger) tss0;
             (:) b t -> Tmbin Fun (f b) (fold_right0 t)}}
         in fold_right0 a1)
        (case h2 of {
          ForallT_nil -> false_rec;
          ForallT_cons x l x0 x1 ->
           eq_rec_r ((:) a0 a1) (\_ ->
             eq_rec_r tss0 (\h3 _ ->
               case h3 of {
                ForallT_nil -> false_rec;
                ForallT_cons x2 l0 x3 x4 ->
                 eq_rec_r a0 (\_ -> eq_rec_r a1 (\h4 _ -> h4) l0) x2 __ x3 x4})
               l) x __ x0 x1})
        (iHa (ForallT_cons a1 tss0
          (case h2 of {
            ForallT_nil -> false_rec;
            ForallT_cons x l x0 x1 ->
             eq_rec_r ((:) a0 a1) (\_ ->
               eq_rec_r tss0 (\h3 _ ->
                 case h3 of {
                  ForallT_nil -> false_rec;
                  ForallT_cons x2 l0 x3 x4 ->
                   eq_rec_r a0 (\_ -> eq_rec_r a1 (\_ h7 -> h7) l0) x2 __ x3
                     x4}) l) x __ x0 x1})
          (case h2 of {
            ForallT_nil -> false_rec;
            ForallT_cons x l x0 x1 ->
             eq_rec_r ((:) a0 a1) (\_ -> eq_rec_r tss0 (\_ h3 -> h3) l) x __
               x0 x1})))) a h1) tss h0) _UU0394_ s k h

sn_preimage2 :: (Ty -> Term0) -> Ty -> (Ty -> Ty -> a1 -> a2) -> (Sn 
                Term0 a2) -> Sn Ty a1
sn_preimage2 h x a b =
  let {v = h x} in
  sn_rect (\_ _ x0 x1 h0 a0 _ -> SNI (\y c ->
    let {c0 = a0 x1 y c} in x0 (h0 y) c0 y h0 a0 __)) v b x h a __

sn_step_nd_to_sn_step :: Ty -> (Sn Term0 Step_nd) -> Sn Ty Step
sn_step_nd_to_sn_step s =
  sn_preimage2 f s f_preserves_step

plutus_ty_strong_normalization :: Ty -> (([]) ((,) BinderTyname Kind)) ->
                                  Kind -> Sn Ty Step
plutus_ty_strong_normalization s _UU0394_ k =
  let {hwk = f_preserves_kind _UU0394_ s k} in
  let {hwk0 = strong_normalization_nd _UU0394_ (f s) k hwk} in
  sn_step_nd_to_sn_step s hwk0

step_dec :: Ty -> (([]) ((,) BinderTyname Kind)) -> Kind -> Prelude.Either
            (SigT Ty Step) ()
step_dec t _UU0394_ k =
  ty_rec (\_ _ _ _ -> Prelude.Right __) (\t1 iHT1 t2 iHT2 _UU0394_0 _ _ ->
    let {o = kind_check _UU0394_0 t1} in
    case o of {
     Prelude.Just k0 ->
      case k0 of {
       Kind_Base ->
        let {o0 = kind_check _UU0394_0 t2} in
        case o0 of {
         Prelude.Just k1 ->
          case k1 of {
           Kind_Base ->
            let {s = iHT1 _UU0394_0 Kind_Base __} in
            case s of {
             Prelude.Left s0 -> Prelude.Left
              (case s0 of {
                ExistT x s1 -> ExistT (Ty_Fun x t2) (Step_funL t1 x t2 s1)});
             Prelude.Right _ ->
              let {s0 = iHT2 _UU0394_0 Kind_Base __} in
              case s0 of {
               Prelude.Left s1 -> Prelude.Left
                (case s1 of {
                  ExistT x s2 -> ExistT (Ty_Fun t1 x) (Step_funR t1 t2 x s2)});
               Prelude.Right _ -> Prelude.Right __}};
           Kind_Arrow _ _ -> false_rec};
         Prelude.Nothing -> false_rec};
       Kind_Arrow _ _ -> false_rec};
     Prelude.Nothing -> false_rec}) (\t1 iHT1 t2 iHT2 _UU0394_0 _ _ ->
    let {o = kind_check _UU0394_0 t2} in
    case o of {
     Prelude.Just k0 ->
      let {o0 = kind_check _UU0394_0 t1} in
      case o0 of {
       Prelude.Just k1 ->
        case k1 of {
         Kind_Base -> false_rec;
         Kind_Arrow k2 k3 ->
          case k2 of {
           Kind_Base -> false_rec;
           Kind_Arrow k4 k5 ->
            case k5 of {
             Kind_Base ->
              case k3 of {
               Kind_Base -> false_rec;
               Kind_Arrow k6 k7 ->
                case k7 of {
                 Kind_Base ->
                  let {b = (Prelude.&&) (kind_eqb k0 k4) (kind_eqb k0 k6)} in
                  case b of {
                   Prelude.True ->
                    let {
                     s = iHT1 _UU0394_0 (Kind_Arrow (Kind_Arrow k4 Kind_Base)
                           (Kind_Arrow k6 Kind_Base)) __}
                    in
                    case s of {
                     Prelude.Left s0 -> Prelude.Left
                      (case s0 of {
                        ExistT x s1 -> ExistT (Ty_IFix x t2) (Step_ifixL t1 x
                         t2 s1)});
                     Prelude.Right _ ->
                      let {s0 = iHT2 _UU0394_0 k0 __} in
                      case s0 of {
                       Prelude.Left s1 -> Prelude.Left
                        (case s1 of {
                          ExistT x s2 -> ExistT (Ty_IFix t1 x) (Step_ifixR t1
                           t2 x s2)});
                       Prelude.Right _ -> Prelude.Right __}};
                   Prelude.False -> false_rec};
                 Kind_Arrow _ _ -> false_rec}};
             Kind_Arrow _ _ -> false_rec}}};
       Prelude.Nothing -> false_rec};
     Prelude.Nothing -> false_rec}) (\b k0 t0 iHT _UU0394_0 _ _ ->
    let {o = kind_check ((:) ((,) b k0) _UU0394_0) t0} in
    case o of {
     Prelude.Just k1 ->
      case k1 of {
       Kind_Base ->
        let {s = iHT ((:) ((,) b k0) _UU0394_0) Kind_Base __} in
        case s of {
         Prelude.Left s0 -> Prelude.Left
          (case s0 of {
            ExistT x s1 -> ExistT (Ty_Forall b k0 x) (Step_forall b k0 t0 x
             s1)});
         Prelude.Right _ -> Prelude.Right __};
       Kind_Arrow _ _ -> false_rec};
     Prelude.Nothing -> false_rec}) (\_ _ _ _ -> Prelude.Right __)
    (\b k0 t0 iHT _UU0394_0 _ _ ->
    let {o = kind_check ((:) ((,) b k0) _UU0394_0) t0} in
    case o of {
     Prelude.Just k1 ->
      let {s = iHT ((:) ((,) b k0) _UU0394_0) k1 __} in
      case s of {
       Prelude.Left s0 -> Prelude.Left
        (case s0 of {
          ExistT x s1 -> ExistT (Ty_Lam b k0 x) (Step_abs b k0 t0 x s1)});
       Prelude.Right _ -> Prelude.Right __};
     Prelude.Nothing -> false_rec}) (\t1 iHT1 t2 iHT2 _UU0394_0 _ _ ->
    let {o = kind_check _UU0394_0 t1} in
    case o of {
     Prelude.Just k0 ->
      case k0 of {
       Kind_Base -> false_rec;
       Kind_Arrow k1 k2 ->
        let {o0 = kind_check _UU0394_0 t2} in
        case o0 of {
         Prelude.Just k3 ->
          let {b = kind_eqb k1 k3} in
          case b of {
           Prelude.True ->
            let {s = iHT1 _UU0394_0 (Kind_Arrow k1 k2) __} in
            case s of {
             Prelude.Left s0 -> Prelude.Left
              (case s0 of {
                ExistT x s1 -> ExistT (Ty_App x t2) (Step_appL t1 x t2 s1)});
             Prelude.Right _ ->
              let {o1 = kind_check _UU0394_0 t1} in
              case o1 of {
               Prelude.Just k4 ->
                case k4 of {
                 Kind_Base -> false_rec;
                 Kind_Arrow k5 _ ->
                  let {o2 = kind_check _UU0394_0 t2} in
                  case o2 of {
                   Prelude.Just k6 ->
                    let {b0 = kind_eqb k5 k6} in
                    case b0 of {
                     Prelude.True ->
                      let {s0 = iHT2 _UU0394_0 k6 __} in
                      case s0 of {
                       Prelude.Left s1 -> Prelude.Left
                        (case s1 of {
                          ExistT x s2 -> ExistT (Ty_App t1 x) (Step_appR t1
                           t2 x s2)});
                       Prelude.Right _ ->
                        ty_rec (\_ _ _ _ _ _ _ -> Prelude.Right __)
                          (\_ _ _ _ _ _ _ _ _ _ -> false_rec)
                          (\_ _ _ _ _ _ _ _ _ _ -> false_rec)
                          (\_ _ _ _ _ _ _ _ _ _ -> false_rec)
                          (\_ _ _ _ _ _ _ -> false_rec)
                          (\b1 k7 t3 _ _ _ _ _ _ _ -> Prelude.Left (ExistT
                          (substituteTCA b1 t2 t3) (Step_beta b1 k7 t3 t2)))
                          (\_ _ _ _ _ _ _ _ _ _ -> Prelude.Right __)
                          (\l _ _ _ _ _ _ ->
                          let {
                           heqo = prop_to_type _UU0394_0 (Ty_SOP l)
                                    (Kind_Arrow k1 k2)}
                          in
                          case heqo of {
                           K_Var_set _UU0394_1 _ _ ->
                            eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __
                              __ __;
                           K_Fun_set _UU0394_1 _ _ x x0 ->
                            eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __
                              __ x x0;
                           K_IFix_set _UU0394_1 _ _ _ x x0 ->
                            eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __
                              __ x x0;
                           K_Forall_set _UU0394_1 _ _ _ x ->
                            eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __
                              __ x;
                           K_Builtin_set _UU0394_1 _ ->
                            eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __
                              __ __;
                           K_Lam_set _UU0394_1 _ _ _ _ x ->
                            eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __
                              __ x;
                           K_App_set _UU0394_1 _ _ _ _ x x0 ->
                            eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __
                              __ x x0;
                           K_SOP_set _UU0394_1 tss x ->
                            eq_rec_r _UU0394_0 (\_ ->
                              eq_rec_r l (\_ -> false_rec) tss) _UU0394_1 __
                              __ x}) t1 iHT1 __ __ __ __ __};
                     Prelude.False -> false_rec};
                   Prelude.Nothing -> false_rec}};
               Prelude.Nothing -> false_rec}};
           Prelude.False -> false_rec};
         Prelude.Nothing -> false_rec}};
     Prelude.Nothing -> false_rec}) (\_ _ _ _ -> Prelude.Right __) t _UU0394_
    k __

type SN = Sn Ty Step

sN_normalise :: Ty -> (([]) ((,) BinderTyname Kind)) -> Kind -> SN -> SigT 
                Ty ()
sN_normalise t _UU0394_ k hSN =
  sn_rec (\t0 _ h _ ->
    let {s0 = step_dec t0 _UU0394_ k} in
    case s0 of {
     Prelude.Left s ->
      case s of {
       ExistT x s1 ->
        let {h0 = h x s1 __} in case h0 of {
                                 ExistT x0 _ -> ExistT x0 __}};
     Prelude.Right _ -> ExistT t0 __}) t hSN __

normaliser_wk :: Ty -> (([]) ((,) BinderTyname Kind)) -> Kind -> Ty
normaliser_wk t _UU0394_ k =
  let {hSN = plutus_ty_strong_normalization t _UU0394_ k} in
  projT1 (sN_normalise t _UU0394_ k hSN)

normaliser :: (([]) ((,) BinderTyname Kind)) -> Ty -> Prelude.Maybe Ty
normaliser _UU0394_ t =
  case kind_check _UU0394_ t of {
   Prelude.Just k -> Prelude.Just (normaliser_wk t _UU0394_ k);
   Prelude.Nothing -> Prelude.Nothing}

map_normaliser :: (([])
                  ((,) ((,) Prelude.String Ty)
                  (([]) ((,) Prelude.String Kind)))) -> Prelude.Maybe
                  (([]) ((,) Prelude.String Ty))
map_normaliser xs =
  case xs of {
   ([]) -> Prelude.Just ([]);
   (:) p xs' ->
    case p of {
     (,) p0 _UU0394_ ->
      case p0 of {
       (,) x t ->
        bind0 (normaliser _UU0394_ t) (\tn ->
          bind0 (map_normaliser xs') (\xs'' -> Prelude.Just ((:) ((,) x tn)
            xs'')))}}}

getTyname :: Tvdecl -> BinderTyname
getTyname tvd =
  case tvd of {
   TyVarDecl x _ -> x}

getKind :: Tvdecl -> Kind
getKind tvd =
  case tvd of {
   TyVarDecl _ k -> k}

ty_Apps :: Ty -> (([]) Ty) -> Ty
ty_Apps f0 xs =
  fold_left (\x x0 -> Ty_App x x0) xs f0

ty_Foralls :: (([]) Tvdecl) -> Ty -> Ty
ty_Foralls xs t =
  fold_right (\yK t' -> Ty_Forall (getTyname yK) (getKind yK) t') t xs

replaceRetTy :: Ty -> Ty -> Ty
replaceRetTy t r =
  case t of {
   Ty_Fun s1 s2 -> Ty_Fun s1 (replaceRetTy s2 r);
   _ -> r}

dtdecl_freshR :: Dtdecl -> Prelude.String
dtdecl_freshR d =
  case d of {
   Datatype _ _ _ cs ->
    let {vars = concat (map (\c -> ftv1 (vdecl_ty c)) cs)} in
    case find
           (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             "R") vars of {
     Prelude.Just _ -> append "R" (concat0 "" vars);
     Prelude.Nothing -> "R"}}

constrLastTyExpected :: Dtdecl -> Ty
constrLastTyExpected dtd =
  case dtd of {
   Datatype xK yKs _ _ ->
    let {x = tvdecl_name xK} in
    let {ys = map tvdecl_name yKs} in
    ty_Apps (Ty_Var x) (map (\x0 -> Ty_Var x0) ys)}

matchTy :: Dtdecl -> Ty
matchTy d =
  let {r = dtdecl_freshR d} in
  case d of {
   Datatype _ yKs _ cs ->
    let {branchTypes = map (\c -> replaceRetTy (vdecl_ty c) (Ty_Var r)) cs}
    in
    let {
     branchTypesFolded = fold_right (\x x0 -> Ty_Fun x x0) (Ty_Var r)
                           branchTypes}
    in
    ty_Foralls yKs (Ty_Fun (constrLastTyExpected d) (Ty_Forall r Kind_Base
      branchTypesFolded))}

constrTy :: Dtdecl -> Vdecl -> Ty
constrTy d c =
  case d of {
   Datatype _ yKs _ _ -> case c of {
                          VarDecl _ t -> ty_Foralls yKs t}}

constrBind :: Dtdecl -> Vdecl -> (,) Prelude.String Ty
constrBind d c =
  case c of {
   VarDecl x _ -> (,) x (constrTy d c)}

constrBinds :: Dtdecl -> ([]) ((,) Prelude.String Ty)
constrBinds d =
  case d of {
   Datatype _ _ _ cs -> rev0 (map (constrBind d) cs)}

matchBind :: Dtdecl -> (,) Prelude.String Ty
matchBind d =
  case d of {
   Datatype _ _ matchFunc _ -> (,) matchFunc (matchTy d)}

binds_Delta :: Binding -> ([]) ((,) Prelude.String Kind)
binds_Delta b =
  case b of {
   TermBind _ _ _ -> ([]);
   TypeBind t _ -> case t of {
                    TyVarDecl x k -> (:) ((,) x k) ([])};
   DatatypeBind d ->
    case d of {
     Datatype t _ _ _ -> case t of {
                          TyVarDecl x k -> (:) ((,) x k) ([])}}}

binds_Gamma :: Binding -> ([]) ((,) Prelude.String Ty)
binds_Gamma b =
  case b of {
   TermBind _ v _ -> case v of {
                      VarDecl x t -> (:) ((,) x t) ([])};
   TypeBind _ _ -> ([]);
   DatatypeBind d ->
    let {constrBs = constrBinds d} in
    let {matchB = matchBind d} in (:) matchB constrBs}

data Builtin_sig =
   BS_Forall Prelude.String Kind Builtin_sig
 | BS_Fun Ty Builtin_sig
 | BS_Result Ty

to_ty :: Builtin_sig -> Ty
to_ty s =
  case s of {
   BS_Forall x k s0 -> Ty_Forall x k (to_ty s0);
   BS_Fun t s0 -> Ty_Fun t (to_ty s0);
   BS_Result t -> t}

to_sig :: DefaultFun -> Builtin_sig
to_sig f0 =
  case f0 of {
   AddInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun (Ty_Builtin
    DefaultUniInteger) (BS_Result (Ty_Builtin DefaultUniInteger)));
   SubtractInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun
    (Ty_Builtin DefaultUniInteger) (BS_Result (Ty_Builtin
    DefaultUniInteger)));
   MultiplyInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun
    (Ty_Builtin DefaultUniInteger) (BS_Result (Ty_Builtin
    DefaultUniInteger)));
   DivideInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun (Ty_Builtin
    DefaultUniInteger) (BS_Result (Ty_Builtin DefaultUniInteger)));
   QuotientInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun
    (Ty_Builtin DefaultUniInteger) (BS_Result (Ty_Builtin
    DefaultUniInteger)));
   EqualsInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun (Ty_Builtin
    DefaultUniInteger) (BS_Result (Ty_Builtin DefaultUniBool)));
   AppendByteString -> BS_Fun (Ty_Builtin DefaultUniByteString) (BS_Fun
    (Ty_Builtin DefaultUniByteString) (BS_Result (Ty_Builtin
    DefaultUniByteString)));
   IfThenElse -> BS_Forall "A" Kind_Base (BS_Fun (Ty_Builtin DefaultUniBool)
    (BS_Fun (Ty_Var "A") (BS_Fun (Ty_Var "A") (BS_Result (Ty_Var "A")))));
   XorByteString -> BS_Fun (Ty_Builtin DefaultUniBool) (BS_Fun (Ty_Builtin
    DefaultUniByteString) (BS_Fun (Ty_Builtin DefaultUniByteString)
    (BS_Result (Ty_Builtin DefaultUniByteString))));
   WriteBits -> BS_Fun (Ty_Builtin DefaultUniByteString) (BS_Fun (Ty_Builtin
    (DefaultUniApply DefaultUniProtoList DefaultUniInteger)) (BS_Fun
    (Ty_Builtin DefaultUniBool) (BS_Result (Ty_Builtin
    DefaultUniByteString))));
   ShiftByteString -> BS_Fun (Ty_Builtin DefaultUniByteString) (BS_Fun
    (Ty_Builtin DefaultUniInteger) (BS_Result (Ty_Builtin
    DefaultUniByteString)));
   RotateByteString -> BS_Fun (Ty_Builtin DefaultUniByteString) (BS_Fun
    (Ty_Builtin DefaultUniInteger) (BS_Result (Ty_Builtin
    DefaultUniByteString)));
   Ripemd_160 -> BS_Fun (Ty_Builtin DefaultUniByteString) (BS_Result
    (Ty_Builtin DefaultUniByteString));
   ReplicateByte -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun (Ty_Builtin
    DefaultUniInteger) (BS_Result (Ty_Builtin DefaultUniByteString)));
   ReadBit -> BS_Fun (Ty_Builtin DefaultUniByteString) (BS_Fun (Ty_Builtin
    DefaultUniInteger) (BS_Result (Ty_Builtin DefaultUniBool)));
   OrByteString -> BS_Fun (Ty_Builtin DefaultUniBool) (BS_Fun (Ty_Builtin
    DefaultUniByteString) (BS_Fun (Ty_Builtin DefaultUniByteString)
    (BS_Result (Ty_Builtin DefaultUniByteString))));
   FindFirstSetBit -> BS_Fun (Ty_Builtin DefaultUniByteString) (BS_Result
    (Ty_Builtin DefaultUniInteger));
   ExpModInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun (Ty_Builtin
    DefaultUniInteger) (BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Result
    (Ty_Builtin DefaultUniInteger))));
   CountSetBits -> BS_Fun (Ty_Builtin DefaultUniByteString) (BS_Result
    (Ty_Builtin DefaultUniInteger));
   ComplementByteString -> BS_Fun (Ty_Builtin DefaultUniByteString)
    (BS_Result (Ty_Builtin DefaultUniByteString));
   AndByteString -> BS_Fun (Ty_Builtin DefaultUniBool) (BS_Fun (Ty_Builtin
    DefaultUniByteString) (BS_Fun (Ty_Builtin DefaultUniByteString)
    (BS_Result (Ty_Builtin DefaultUniByteString))));
   _ -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Result (Ty_Builtin
    DefaultUniInteger))}

lookupBuiltinTy :: DefaultFun -> Ty
lookupBuiltinTy f0 =
  to_ty (to_sig f0)

flatten :: (([]) (([]) a1)) -> ([]) a1
flatten l =
  concat (rev0 l)

fromDecl :: Tvdecl -> (,) Prelude.String Kind
fromDecl tvd =
  case tvd of {
   TyVarDecl v k -> (,) v k}

freshUnwrapIFix :: Ty -> Prelude.String
freshUnwrapIFix f0 =
  append "a" (concat0 "" (ftv1 f0))

unwrapIFix :: Ty -> Kind -> Ty -> Ty
unwrapIFix f0 k t =
  let {b = freshUnwrapIFix f0} in
  Ty_App (Ty_App f0 (Ty_Lam b k (Ty_IFix f0 (Ty_Var b)))) t

drop_ty_var' :: Prelude.String -> (([]) ((,) Prelude.String Ty)) -> (([])
                Prelude.String) -> ([]) ((,) Prelude.String Ty)
drop_ty_var' x _UU0393_ acc =
  case _UU0393_ of {
   ([]) -> ([]);
   (:) p _UU0393_' ->
    case p of {
     (,) x0 t ->
      case in_dec
             ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             x (ftv1 t) of {
       Prelude.True -> drop_ty_var' x _UU0393_' ((:) x0 acc);
       Prelude.False ->
        case in_dec
               ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
               x0 acc of {
         Prelude.True -> drop_ty_var' x _UU0393_' acc;
         Prelude.False -> (:) ((,) x0 t) (drop_ty_var' x _UU0393_' acc)}}}}

drop_ty_var :: Prelude.String -> (([]) ((,) Prelude.String Ty)) -> ([])
               ((,) Prelude.String Ty)
drop_ty_var x _UU0393_ =
  drop_ty_var' x _UU0393_ ([])

drop__UU0394_' :: (([]) ((,) Prelude.String Kind)) -> (([]) Prelude.String)
                  -> ([]) ((,) Prelude.String Kind)
drop__UU0394_' _UU0394_ bsn =
  filter (\x -> Prelude.not (inb_string (fst x) bsn)) _UU0394_

drop__UU0394_ :: (([]) ((,) Prelude.String Kind)) -> (([]) Binding) -> ([])
                 ((,) Prelude.String Kind)
drop__UU0394_ _UU0394_ bs =
  drop__UU0394_' _UU0394_ (btvbs bs)

insert_deltas_rec :: (([]) ((,) Prelude.String Ty)) -> (([])
                     ((,) Prelude.String Kind)) -> ([])
                     ((,) ((,) Prelude.String Ty)
                     (([]) ((,) Prelude.String Kind)))
insert_deltas_rec xs _UU0394_ =
  case xs of {
   ([]) -> ([]);
   (:) p xs' -> (:) ((,) p _UU0394_) (insert_deltas_rec xs' _UU0394_)}

insert_deltas_bind_Gamma_nr :: (([]) Binding) -> (([])
                               ((,) BinderTyname Kind)) -> ([])
                               ((,) ((,) BinderName Ty)
                               (([]) ((,) BinderTyname Kind)))
insert_deltas_bind_Gamma_nr bs _UU0394_ =
  case bs of {
   ([]) -> ([]);
   (:) b bs' ->
    app (insert_deltas_bind_Gamma_nr bs' (app (binds_Delta b) _UU0394_))
      (insert_deltas_rec (binds_Gamma b) (app (binds_Delta b) _UU0394_))}

no_dup_fun :: (([]) Prelude.String) -> Prelude.Bool
no_dup_fun xs =
  case xs of {
   ([]) -> Prelude.True;
   (:) x xs0 ->
    case in_dec
           ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           x xs0 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> no_dup_fun xs0}}

is_KindBase :: (Prelude.Maybe Kind) -> Prelude.Bool
is_KindBase k =
  case k of {
   Prelude.Just k0 ->
    case k0 of {
     Kind_Base -> Prelude.True;
     Kind_Arrow _ _ -> Prelude.False};
   Prelude.Nothing -> Prelude.False}

constructor_well_formed_check :: (([]) ((,) BinderTyname Kind)) -> Vdecl ->
                                 Ty -> Prelude.Bool
constructor_well_formed_check _UU0394_ v tr =
  case v of {
   VarDecl _ t ->
    case splitTy t of {
     (,) targs tr' ->
      (Prelude.&&) (ty_eqb tr tr')
        (forallb (\u -> is_KindBase (kind_check _UU0394_ u)) targs)}}

binding_well_formed_check :: ((([]) ((,) BinderTyname Kind)) -> (([])
                             ((,) BinderName Ty)) -> Term -> Prelude.Maybe
                             Ty) -> (([]) ((,) BinderTyname Kind)) -> (([])
                             ((,) BinderName Ty)) -> Recursivity -> Binding
                             -> Prelude.Bool
binding_well_formed_check type_check' _UU0394_ _UU0393_ rec0 binding =
  case binding of {
   TermBind _ v t ->
    case v of {
     VarDecl _ t0 ->
      case kind_check _UU0394_ t0 of {
       Prelude.Just k ->
        case k of {
         Kind_Base ->
          case type_check' _UU0394_ _UU0393_ t of {
           Prelude.Just tn ->
            case normaliser _UU0394_ t0 of {
             Prelude.Just tn' -> ty_eqb tn tn';
             Prelude.Nothing -> Prelude.False};
           Prelude.Nothing -> Prelude.False};
         Kind_Arrow _ _ -> Prelude.False};
       Prelude.Nothing -> Prelude.False}};
   TypeBind t t0 ->
    case t of {
     TyVarDecl _ k ->
      case kind_check _UU0394_ t0 of {
       Prelude.Just k' -> kind_eqb k k';
       Prelude.Nothing -> Prelude.False}};
   DatatypeBind d ->
    case d of {
     Datatype xK yKs matchFunc cs ->
      let {dtd = Datatype xK yKs matchFunc cs} in
      let {x = tvdecl_name xK} in
      let {ys = map tvdecl_name yKs} in
      case (Prelude.&&) (no_dup_fun ((:) x ys))
             (no_dup_fun (map vdecl_name cs)) of {
       Prelude.True ->
        let {
         _UU0394__ns = case rec0 of {
                        NonRec -> drop__UU0394_' _UU0394_ ((:) x ([]));
                        Rec -> _UU0394_}}
        in
        let {_UU0394_' = app (rev0 (map fromDecl yKs)) _UU0394__ns} in
        let {tres = constrLastTyExpected dtd} in
        case forallb (\c -> constructor_well_formed_check _UU0394_' c tres)
               cs of {
         Prelude.True ->
          case rec0 of {
           NonRec ->
            case kind_check ((:) (fromDecl xK) _UU0394_') tres of {
             Prelude.Just k ->
              case k of {
               Kind_Base -> Prelude.True;
               Kind_Arrow _ _ -> Prelude.False};
             Prelude.Nothing -> Prelude.False};
           Rec ->
            case kind_check _UU0394_' tres of {
             Prelude.Just k ->
              case k of {
               Kind_Base -> Prelude.True;
               Kind_Arrow _ _ -> Prelude.False};
             Prelude.Nothing -> Prelude.False}};
         Prelude.False -> Prelude.False};
       Prelude.False -> Prelude.False}}}

bindings_well_formed_nonrec_check :: ((([]) ((,) BinderTyname Kind)) -> (([])
                                     ((,) BinderName Ty)) -> Recursivity ->
                                     Binding -> Prelude.Bool) -> (([])
                                     ((,) BinderTyname Kind)) -> (([])
                                     ((,) BinderName Ty)) -> (([]) Binding)
                                     -> Prelude.Bool
bindings_well_formed_nonrec_check b_wf _UU0394_ _UU0393_ bs =
  case bs of {
   ([]) -> Prelude.True;
   (:) b bs' ->
    case map_normaliser
           (insert_deltas_rec (binds_Gamma b) (app (binds_Delta b) _UU0394_)) of {
     Prelude.Just bsGn ->
      (Prelude.&&) (b_wf _UU0394_ _UU0393_ NonRec b)
        (bindings_well_formed_nonrec_check b_wf
          (app (binds_Delta b) _UU0394_) (app bsGn _UU0393_) bs');
     Prelude.Nothing -> Prelude.False}}

bindings_well_formed_rec_check :: (Binding -> Prelude.Bool) -> (([]) 
                                  Binding) -> Prelude.Bool
bindings_well_formed_rec_check b_wf bs =
  case bs of {
   ([]) -> Prelude.True;
   (:) b bs' ->
    (Prelude.&&) (b_wf b) (bindings_well_formed_rec_check b_wf bs')}

type_check :: (([]) ((,) BinderTyname Kind)) -> (([]) ((,) BinderName Ty)) ->
              Term -> Prelude.Maybe Ty
type_check _UU0394_ _UU0393_ term =
  case term of {
   Let r bs t ->
    case r of {
     NonRec ->
      let {_UU0394_' = app (flatten (map binds_Delta bs)) _UU0394_} in
      let {xs = insert_deltas_bind_Gamma_nr bs _UU0394_} in
      bind (map_normaliser xs) (\bsgn ->
        let {_UU0393_' = app bsgn _UU0393_} in
        case bindings_well_formed_nonrec_check
               (binding_well_formed_check type_check) _UU0394_ _UU0393_ bs of {
         Prelude.True ->
          bind (type_check _UU0394_' _UU0393_' t) (\t0 ->
            let {_UU0394__no_esc = drop__UU0394_ _UU0394_ bs} in
            case kind_check _UU0394__no_esc t0 of {
             Prelude.Just k ->
              case k of {
               Kind_Base -> Prelude.Just t0;
               Kind_Arrow _ _ -> Prelude.Nothing};
             Prelude.Nothing -> Prelude.Nothing});
         Prelude.False -> Prelude.Nothing});
     Rec ->
      case (Prelude.&&) (no_dup_fun (btvbs bs)) (no_dup_fun (bvbs bs)) of {
       Prelude.True ->
        let {_UU0394_' = app (flatten (map binds_Delta bs)) _UU0394_} in
        let {xs = insert_deltas_rec (flatten (map binds_Gamma bs)) _UU0394_'}
        in
        bind (map_normaliser xs) (\bsgn ->
          let {_UU0393_' = app bsgn _UU0393_} in
          case bindings_well_formed_rec_check
                 (binding_well_formed_check type_check _UU0394_' _UU0393_'
                   Rec) bs of {
           Prelude.True ->
            bind (type_check _UU0394_' _UU0393_' t) (\t0 ->
              let {_UU0394__no_esc = drop__UU0394_ _UU0394_ bs} in
              case kind_check _UU0394__no_esc t0 of {
               Prelude.Just k ->
                case k of {
                 Kind_Base -> Prelude.Just t0;
                 Kind_Arrow _ _ -> Prelude.Nothing};
               Prelude.Nothing -> Prelude.Nothing});
           Prelude.False -> Prelude.Nothing});
       Prelude.False -> Prelude.Nothing}};
   Var x ->
    bind (lookup x _UU0393_) (\t ->
      case kind_check _UU0394_ t of {
       Prelude.Just k ->
        case k of {
         Kind_Base -> normaliser _UU0394_ t;
         Kind_Arrow _ _ -> Prelude.Nothing};
       Prelude.Nothing -> Prelude.Nothing});
   TyAbs x k t ->
    case type_check ((:) ((,) x k) _UU0394_) (drop_ty_var x _UU0393_) t of {
     Prelude.Just t0 -> Prelude.Just (Ty_Forall x k t0);
     Prelude.Nothing -> Prelude.Nothing};
   LamAbs x t1 t ->
    bind (normaliser _UU0394_ t1) (\t1n ->
      case type_check _UU0394_ ((:) ((,) x t1n) _UU0393_) t of {
       Prelude.Just t2 ->
        case kind_check _UU0394_ t1 of {
         Prelude.Just k ->
          case k of {
           Kind_Base -> Prelude.Just (Ty_Fun t1n t2);
           Kind_Arrow _ _ -> Prelude.Nothing};
         Prelude.Nothing -> Prelude.Nothing};
       Prelude.Nothing -> Prelude.Nothing});
   Apply t1 t2 ->
    case type_check _UU0394_ _UU0393_ t1 of {
     Prelude.Just t ->
      case t of {
       Ty_Fun t3 t4 ->
        case type_check _UU0394_ _UU0393_ t2 of {
         Prelude.Just t1' ->
          case ty_eqb t3 t1' of {
           Prelude.True -> Prelude.Just t4;
           Prelude.False -> Prelude.Nothing};
         Prelude.Nothing -> Prelude.Nothing};
       _ -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   Constant0 c -> case c of {
                   ValueOf t _ -> Prelude.Just (Ty_Builtin t)};
   Builtin f0 ->
    let {t = lookupBuiltinTy f0} in
    bind (normaliser _UU0394_ t) (\tn -> Prelude.Just tn);
   TyInst t1 t2 ->
    case type_check _UU0394_ _UU0393_ t1 of {
     Prelude.Just t ->
      case t of {
       Ty_Forall x k2 t3 ->
        case kind_check _UU0394_ t2 of {
         Prelude.Just k2' ->
          case kind_eqb k2 k2' of {
           Prelude.True ->
            bind (normaliser _UU0394_ t2) (\t2n ->
              bind (normaliser _UU0394_ (substituteTCA x t2n t3)) (\t0n ->
                Prelude.Just t0n));
           Prelude.False -> Prelude.Nothing};
         Prelude.Nothing -> Prelude.Nothing};
       _ -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   Error s' ->
    bind (normaliser _UU0394_ s') (\s'n ->
      case kind_check _UU0394_ s' of {
       Prelude.Just k ->
        case k of {
         Kind_Base -> Prelude.Just s'n;
         Kind_Arrow _ _ -> Prelude.Nothing};
       Prelude.Nothing -> Prelude.Nothing});
   IWrap f0 t m ->
    case kind_check _UU0394_ t of {
     Prelude.Just k ->
      case kind_check _UU0394_ f0 of {
       Prelude.Just k0 ->
        case k0 of {
         Kind_Base -> Prelude.Nothing;
         Kind_Arrow k1 k2 ->
          case k1 of {
           Kind_Base -> Prelude.Nothing;
           Kind_Arrow k' k3 ->
            case k3 of {
             Kind_Base ->
              case k2 of {
               Kind_Base -> Prelude.Nothing;
               Kind_Arrow k'' k4 ->
                case k4 of {
                 Kind_Base ->
                  case type_check _UU0394_ _UU0393_ m of {
                   Prelude.Just t0n ->
                    case (Prelude.&&) (kind_eqb k k') (kind_eqb k k'') of {
                     Prelude.True ->
                      bind (normaliser _UU0394_ t) (\tn ->
                        bind (normaliser _UU0394_ f0) (\fn ->
                          bind (normaliser _UU0394_ (unwrapIFix fn k tn))
                            (\t0n' ->
                            case ty_eqb t0n t0n' of {
                             Prelude.True -> Prelude.Just (Ty_IFix fn tn);
                             Prelude.False -> Prelude.Nothing})));
                     Prelude.False -> Prelude.Nothing};
                   Prelude.Nothing -> Prelude.Nothing};
                 Kind_Arrow _ _ -> Prelude.Nothing}};
             Kind_Arrow _ _ -> Prelude.Nothing}}};
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   Unwrap m ->
    case type_check _UU0394_ _UU0393_ m of {
     Prelude.Just t ->
      case t of {
       Ty_IFix f0 t0 ->
        case kind_check _UU0394_ t0 of {
         Prelude.Just k ->
          bind (normaliser _UU0394_ (unwrapIFix f0 k t0)) (\t0n ->
            Prelude.Just t0n);
         Prelude.Nothing -> Prelude.Nothing};
       _ -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   _ -> Prelude.Nothing}

ast :: Term
ast =
  Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1)))))))) (Ty_Fun (Ty_Builtin DefaultUniBool) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniByteString))))) (Builtin XorByteString)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList)
    (Ty_Builtin DefaultUniInteger)) (Ty_Fun (Ty_Builtin DefaultUniBool)
    (Ty_Builtin DefaultUniByteString))))) (Builtin WriteBits)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1)))))))
    (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniBool))))) (Builtin
    VerifySchnorrSecp256k1Signature)) ([])) (Let NonRec ((:) (TermBind Strict
    (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1)))))))
    (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniBool))))) (Builtin VerifyEd25519Signature)) ([]))
    (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1)))))))
    (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniBool))))) (Builtin VerifyEcdsaSecp256k1Signature))
    ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))))))))
    (Ty_Fun (Ty_Builtin DefaultUniData) (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_App (Ty_App (Ty_Builtin DefaultUniProtoPair)
    (Ty_Builtin DefaultUniData)) (Ty_Builtin DefaultUniData))))) (Builtin
    UnMapData)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Fun (Ty_Builtin DefaultUniData)
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Builtin DefaultUniData))))
    (Builtin UnListData)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Fun (Ty_Builtin DefaultUniData)
    (Ty_Builtin DefaultUniInteger))) (Builtin UnIData)) ([])) (Let NonRec
    ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Fun (Ty_Builtin DefaultUniData)
    (Ty_App (Ty_App (Ty_Builtin DefaultUniProtoPair) (Ty_Builtin
    DefaultUniInteger)) (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Builtin
    DefaultUniData))))) (Builtin UnConstrData)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Fun (Ty_Builtin DefaultUniData)
    (Ty_Builtin DefaultUniByteString))) (Builtin UnBData)) ([])) (Let NonRec
    ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))) (Ty_Builtin DefaultUniUnit)) (Constant0
    (some (ValueOf DefaultUniUnit (unsafeCoerce ()))))) ([])) (Let NonRec
    ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))) (Ty_Builtin
    DefaultUniBool)) (Constant0
    (some (ValueOf DefaultUniBool (unsafeCoerce Prelude.True))))) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))) Kind_Base (Ty_Fun
    (Ty_Builtin DefaultUniString) (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) (Builtin Trace)) ([]))
    (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))))) Kind_Base (Ty_Fun (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))))))) (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))))))) (Builtin TailList)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger)))) (Builtin SubtractInteger)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))))) Kind_Base (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))))) Kind_Base (Ty_Fun (Ty_App (Ty_App (Ty_Builtin
    DefaultUniProtoPair) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1)))))))))))) (Builtin SndPair)) ([])) (Let NonRec ((:) (TermBind
    Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))) (Ty_Fun (Ty_Builtin DefaultUniInteger)
    (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))))) (Builtin
    SliceByteString)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniByteString)))) (Builtin ShiftByteString)) ([])) (Let NonRec
    ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1)))))))
    (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Builtin
    DefaultUniByteString))) (Builtin Sha3_256)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1)))))))
    (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Builtin
    DefaultUniByteString))) (Builtin Sha2_256)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Fun (Ty_Builtin DefaultUniData)
    (Ty_Builtin DefaultUniByteString))) (Builtin SerialiseData)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniByteString)))) (Builtin RotateByteString)) ([])) (Let NonRec
    ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))) (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Builtin
    DefaultUniByteString))) (Builtin Ripemd_160)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1)))))))) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Builtin DefaultUniByteString)))) (Builtin
    ReplicateByte)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger)))) (Builtin RemainderInteger)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniBool)))) (Builtin ReadBit)) ([])) (Let NonRec ((:) (TermBind
    Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1)))))) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Builtin DefaultUniInteger)))) (Builtin
    QuotientInteger)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBool) (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniByteString)))))
    (Builtin OrByteString)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))) Kind_Base
    (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))))) (Ty_Builtin
    DefaultUniBool)))) (Builtin NullList)) ([])) (Let NonRec ((:) (TermBind
    Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger)))) (Builtin MultiplyInteger)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger)))) (Builtin ModInteger)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Fun (Ty_Builtin DefaultUniData)
    (Ty_Fun (Ty_Builtin DefaultUniData) (Ty_App (Ty_App (Ty_Builtin
    DefaultUniProtoPair) (Ty_Builtin DefaultUniData)) (Ty_Builtin
    DefaultUniData))))) (Builtin MkPairData)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniUnit) (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_App (Ty_App
    (Ty_Builtin DefaultUniProtoPair) (Ty_Builtin DefaultUniData)) (Ty_Builtin
    DefaultUniData))))) (Builtin MkNilPairData)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Fun (Ty_Builtin DefaultUniUnit)
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Builtin DefaultUniData))))
    (Builtin MkNilData)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Fun (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_App (Ty_App (Ty_Builtin DefaultUniProtoPair)
    (Ty_Builtin DefaultUniData)) (Ty_Builtin DefaultUniData))) (Ty_Builtin
    DefaultUniData))) (Builtin MapData)) ([])) (Let NonRec ((:) (TermBind
    Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))))))))
    (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Builtin
    DefaultUniData)) (Ty_Builtin DefaultUniData))) (Builtin ListData)) ([]))
    (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Fun (Ty_Builtin DefaultUniInteger)
    (Ty_Builtin DefaultUniData))) (Builtin IData)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Fun (Ty_Builtin DefaultUniInteger)
    (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Builtin
    DefaultUniData)) (Ty_Builtin DefaultUniData)))) (Builtin ConstrData))
    ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))) Kind_Base (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))) (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))))) (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))))))))) (Builtin MkCons)) ([])) (Let NonRec ((:) (TermBind
    Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniData))) (Builtin BData))
    ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Builtin DefaultUniBool)))) (Builtin
    LessThanInteger)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))) (Ty_Fun (Ty_Builtin DefaultUniInteger)
    (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin DefaultUniBool))))
    (Builtin LessThanEqualsInteger)) ([])) (Let NonRec ((:) (TermBind Strict
    (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1)))))))
    (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniBool)))) (Builtin
    LessThanEqualsByteString)) ([])) (Let NonRec ((:) (TermBind Strict
    (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniBool)))) (Builtin LessThanByteString)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniInteger)))
    (Builtin LengthOfByteString)) ([])) (Let NonRec ((:) (TermBind NonStrict
    (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) Kind_Base
    (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))))) (TyAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) Kind_Base (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))))))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))))))) ([])) (Let NonRec ((:) (TermBind
    Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))) Kind_Base (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))) Kind_Base
    (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun
    (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))) (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))) (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))))))) (TyAbs
    (show_Z 0) Kind_Base (TyAbs (show_Z ((\x -> x) 1)) Kind_Base (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))
    (Ty_Var (show_Z ((\x -> x) 1))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))) (Ty_Fun (Ty_Var (show_Z 0)) (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var (show_Z 0))) (Ty_Var
    (show_Z ((\x -> x) 1))))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))) (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Var (show_Z 0))) (TyInst (Apply
    (Apply (Apply (TyInst (TyInst (Builtin ChooseList) (Ty_Var (show_Z 0)))
    (Ty_Forall (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) 1))) Kind_Base
    (Ty_Var (show_Z ((\x -> x) 1))))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))) (TyAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) 1))) Kind_Base (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))
    (TyAbs (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) 1))) Kind_Base (Apply
    (Apply (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1))))) (Apply (TyInst (Builtin HeadList) (Ty_Var
    (show_Z 0))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))) (Apply
    (TyInst (Builtin TailList) (Ty_Var (show_Z 0))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Var
    (show_Z ((\x -> x) 1)))))))))) ([])) (Let NonRec ((:) (TermBind Strict
    (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))
    (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Builtin DefaultUniInteger)))) (Builtin
    AddInteger)) ([])) (Let NonRec ((:) (TypeBind (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))) (Kind_Arrow Kind_Base
    Kind_Base)) (Ty_Builtin DefaultUniProtoList)) ([])) (Let NonRec ((:)
    (TypeBind (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))) Kind_Base) (Ty_Builtin DefaultUniData))
    ([])) (Let NonRec ((:) (TypeBind (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) (Kind_Arrow Kind_Base Kind_Base))
    (Ty_Lam
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) Kind_Base (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Builtin DefaultUniData)))) ([])) (Let NonRec
    ((:) (TypeBind (TyVarDecl (show_Z ((\x -> x) 1)) Kind_Base) (Ty_Builtin
    DefaultUniInteger)) ([])) (Let NonRec ((:) (TermBind NonStrict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) Kind_Base (Ty_Fun (Ty_App (Ty_Lam
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) Kind_Base (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Builtin DefaultUniData))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))))) (Ty_Builtin DefaultUniInteger))))
    (TyAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) Kind_Base
    (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_App
    (Ty_Lam
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) Kind_Base (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Builtin DefaultUniData))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))) (Let NonRec
    ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Builtin DefaultUniData))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) Kind_Base (Ty_Fun (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Builtin DefaultUniInteger))))) (TyAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))) Kind_Base (Let Rec ((:) (TermBind NonStrict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))))) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger)))) (Apply (Apply (TyInst (TyInst (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))))) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger))) (TyInst (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))))) (Ty_Builtin
    DefaultUniInteger))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))))) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))))))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))) ([])) (Let
    NonRec ((:) (TermBind NonStrict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Builtin
    DefaultUniInteger)) (Constant0
    (some (ValueOf DefaultUniInteger (unsafeCoerce ((\x -> x) 1)))))) ([]))
    (Let NonRec ((:) (TermBind NonStrict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Builtin DefaultUniInteger))) (Apply
    (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))))))) ([]))
    (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Builtin DefaultUniInteger) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Builtin DefaultUniInteger))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Builtin
    DefaultUniInteger)) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))))) ([])) (Let NonRec ((:) (TermBind
    Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Builtin
    DefaultUniInteger)) (Apply (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))))))) ([]))
    (Apply (Apply (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))))))))))))))))))
    ([])) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))))) ([]))
    (Apply (Apply (TyInst (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))))) (Ty_Builtin
    DefaultUniData)) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))) (Constant0
    (some (ValueOf DefaultUniInteger (unsafeCoerce 0)))))))))) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))) (Builtin
    Keccak_256)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1)))))))) (Ty_Fun (Ty_Builtin DefaultUniBool) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniByteString))))) (Builtin IntegerToByteString)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Builtin DefaultUniInteger))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))) (Ty_Builtin DefaultUniInteger) (Apply (Apply (Builtin
    SubtractInteger) (Constant0
    (some (ValueOf DefaultUniInteger (unsafeCoerce 0))))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1))))))))))))) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniInteger)
    (Ty_Builtin DefaultUniInteger)))) (Builtin IndexByteString)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))
    (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))) Kind_Base (Ty_Fun
    (Ty_Builtin DefaultUniBool) (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Builtin IfThenElse))
    ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))) Kind_Base
    (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))))))) (Builtin
    HeadList)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))))) Kind_Base (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))))) Kind_Base (Ty_Fun (Ty_App (Ty_App (Ty_Builtin
    DefaultUniProtoPair) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1)))))))))))) (Builtin FstPair)) ([])) (Let NonRec ((:) (TermBind
    Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniInteger)))
    (Builtin FindFirstSetBit)) ([])) (Let NonRec ((:) (TermBind Strict
    (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))) (Ty_Builtin DefaultUniBool)) (Constant0
    (some (ValueOf DefaultUniBool (unsafeCoerce Prelude.False))))) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Builtin DefaultUniInteger)))))
    (Builtin ExpModInteger)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))
    Kind_Base (Ty_Fun (Ty_Builtin DefaultUniUnit) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))
    (TyAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1)))))
    Kind_Base (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))) (Ty_Builtin DefaultUniUnit)
    (Error (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))))))))))
    ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))) (Ty_Fun (Ty_Builtin
    DefaultUniString) (Ty_Fun (Ty_Builtin DefaultUniString) (Ty_Builtin
    DefaultUniBool)))) (Builtin EqualsString)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniBool)))) (Builtin EqualsInteger)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))))))))
    (Ty_Fun (Ty_Builtin DefaultUniData) (Ty_Fun (Ty_Builtin DefaultUniData)
    (Ty_Builtin DefaultUniBool)))) (Builtin EqualsData)) ([])) (Let NonRec
    ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniBool)))) (Builtin
    EqualsByteString)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))
    (Ty_Fun (Ty_Builtin DefaultUniString) (Ty_Builtin DefaultUniByteString)))
    (Builtin EncodeUtf8)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))) (Ty_Builtin DefaultUniString))
    (Constant0 (some (ValueOf DefaultUniString (unsafeCoerce ([])))))) ([]))
    (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))) (Ty_Builtin DefaultUniByteString))
    (Constant0 (some (ValueOf DefaultUniByteString (unsafeCoerce ([]))))))
    ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger)))) (Builtin DivideInteger)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))
    (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniString)))
    (Builtin DecodeUtf8)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniInteger))) (Builtin
    CountSetBits)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniByteString)))) (Builtin ConsByteString)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))) (Builtin
    ComplementByteString)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))
    (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))
    Kind_Base (Ty_Fun (Ty_Builtin DefaultUniUnit) (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))
    (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))
    (Builtin ChooseUnit)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))))) Kind_Base (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))) Kind_Base
    (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))))))) (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun
    (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))))))) (Builtin
    ChooseList)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))))) Kind_Base (Ty_Fun (Ty_Builtin
    DefaultUniData) (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))))))))))))))) (Builtin ChooseData)) ([]))
    (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))))))))
    (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))))))))
    Kind_Base (Ty_Fun (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Builtin DefaultUniData)) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1)))))))))))
    (Ty_Fun (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_App (Ty_App
    (Ty_Builtin DefaultUniProtoPair) (Ty_Builtin DefaultUniData)) (Ty_Builtin
    DefaultUniData))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))))))))))
    (Ty_Fun (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Builtin
    DefaultUniData)) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))))))))))
    (Ty_Fun (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))))))))))
    (Ty_Fun (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))))))))))
    (Ty_Fun (Ty_Builtin DefaultUniData) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1)))))))))))))))))
    (TyAbs (show_Z 0) Kind_Base (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) 1))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList)
    (Ty_Builtin DefaultUniData)) (Ty_Var (show_Z 0)))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))) (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_App (Ty_App (Ty_Builtin
    DefaultUniProtoPair) (Ty_Builtin DefaultUniData)) (Ty_Builtin
    DefaultUniData))) (Ty_Var (show_Z 0))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))
    (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Builtin
    DefaultUniData)) (Ty_Var (show_Z 0))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))) (Ty_Fun (Ty_Builtin DefaultUniInteger)
    (Ty_Var (show_Z 0))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Var (show_Z 0))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))) (Ty_Builtin DefaultUniData)
    (TyInst (Apply (Apply (Apply (Apply (Apply (Apply (TyInst (Builtin
    ChooseData) (Ty_Forall (show_Z ((\x -> x) 1)) Kind_Base (Ty_Var
    (show_Z 0)))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))) (TyAbs
    (show_Z ((\x -> x) 1)) Kind_Base (Apply (Apply (TyInst (TyInst (TyInst
    (TyAbs (show_Z 0) Kind_Base (TyAbs (show_Z ((\x -> x) 1)) Kind_Base
    (TyAbs (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) 1))) Kind_Base (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))) (Ty_Fun
    (Ty_Var (show_Z 0)) (Ty_Fun (Ty_Var (show_Z ((\x -> x) 1))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) 1)))))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))
    (Ty_App (Ty_App (Ty_Builtin DefaultUniProtoPair) (Ty_Var (show_Z 0)))
    (Ty_Var (show_Z ((\x -> x) 1)))) (Apply (Apply (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))) (Apply
    (TyInst (TyInst (Builtin FstPair) (Ty_Var (show_Z 0))) (Ty_Var
    (show_Z ((\x -> x) 1)))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))
    (Apply (TyInst (TyInst (Builtin SndPair) (Ty_Var (show_Z 0))) (Ty_Var
    (show_Z ((\x -> x) 1)))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))))))
    (Ty_Builtin DefaultUniInteger)) (Ty_App (Ty_Builtin DefaultUniProtoList)
    (Ty_Builtin DefaultUniData))) (Ty_Var (show_Z 0))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) 1))))) (Apply (Builtin
    UnConstrData) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))) (TyAbs
    (show_Z ((\x -> x) 1)) Kind_Base (Apply (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))) (Apply
    (Builtin UnMapData) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))) (TyAbs
    (show_Z ((\x -> x) 1)) Kind_Base (Apply (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))
    (Apply (Builtin UnListData) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))) (TyAbs
    (show_Z ((\x -> x) 1)) Kind_Base (Apply (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1))))) (Apply (Builtin UnIData) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))) (TyAbs
    (show_Z ((\x -> x) 1)) Kind_Base (Apply (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))) (Apply (Builtin UnBData) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))) (Ty_Var
    (show_Z 0))))))))))) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBool) (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Builtin
    DefaultUniInteger)))) (Builtin ByteStringToInteger)) ([])) (Let NonRec
    ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1)))))))) (Ty_Fun (Ty_Builtin DefaultUniBLS12_381_MlResult) (Ty_Fun
    (Ty_Builtin DefaultUniBLS12_381_MlResult) (Ty_Builtin
    DefaultUniBLS12_381_MlResult)))) (Builtin Bls12_381_mulMlResult)) ([]))
    (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G1_Element) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Builtin
    DefaultUniBLS12_381_MlResult)))) (Builtin Bls12_381_millerLoop)) ([]))
    (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      1)))))))) (Ty_Fun (Ty_Builtin DefaultUniBLS12_381_MlResult) (Ty_Fun
    (Ty_Builtin DefaultUniBLS12_381_MlResult) (Ty_Builtin DefaultUniBool))))
    (Builtin Bls12_381_finalVerify)) ([])) (Let NonRec ((:) (TermBind Strict
    (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniBLS12_381_G2_Element)))
    (Builtin Bls12_381_G2_uncompress)) ([])) (Let NonRec ((:) (TermBind
    Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniBLS12_381_G2_Element)
    (Ty_Builtin DefaultUniBLS12_381_G2_Element)))) (Builtin
    Bls12_381_G2_scalarMul)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Builtin
    DefaultUniBLS12_381_G2_Element))) (Builtin Bls12_381_G2_neg)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))
    (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniBLS12_381_G2_Element))))
    (Builtin Bls12_381_G2_hashToGroup)) ([])) (Let NonRec ((:) (TermBind
    Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Builtin DefaultUniBool)))) (Builtin
    Bls12_381_G2_equal)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))) (Ty_Builtin DefaultUniByteString))
    (Constant0
    (some (ValueOf DefaultUniByteString
      (unsafeCoerce ((:) '\xc0' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ([]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))) (Ty_Builtin DefaultUniByteString))
    (Constant0
    (some (ValueOf DefaultUniByteString
      (unsafeCoerce ((:) '\x93' ((:) '\xe0' ((:) '+' ((:) '`' ((:) 'R' ((:)
        'q' ((:) '\x9f' ((:) '`' ((:) '}' ((:) '\xac' ((:) '\xd3' ((:) '\xa0'
        ((:) '\x88' ((:) '\'' ((:) 'O' ((:) 'e' ((:) 'Y' ((:) 'k' ((:) '\xd0'
        ((:) '\xd0' ((:) '\x99' ((:) ' ' ((:) '\xb6' ((:) '\x1a' ((:) '\xb5'
        ((:) '\xda' ((:) 'a' ((:) '\xbb' ((:) '\xdc' ((:) '\x7f' ((:) 'P'
        ((:) 'I' ((:) '3' ((:) 'L' ((:) '\xf1' ((:) '\x12' ((:) '\x13' ((:)
        '\x94' ((:) ']' ((:) 'W' ((:) '\xe5' ((:) '\xac' ((:) '}' ((:) '\x05'
        ((:) ']' ((:) '\x04' ((:) '+' ((:) '~' ((:) '\x02' ((:) 'J' ((:)
        '\xa2' ((:) '\xb2' ((:) '\xf0' ((:) '\x8f' ((:) '\n' ((:) '\x91' ((:)
        '&' ((:) '\x08' ((:) '\x05' ((:) '\'' ((:) '-' ((:) '\xc5' ((:)
        '\x10' ((:) 'Q' ((:) '\xc6' ((:) '\xe4' ((:) 'z' ((:) '\xd4' ((:)
        '\xfa' ((:) '@' ((:) ';' ((:) '\x02' ((:) '\xb4' ((:) 'Q' ((:) '\x0b'
        ((:) 'd' ((:) 'z' ((:) '\xe3' ((:) '\xd1' ((:) 'w' ((:) '\x0b' ((:)
        '\xac' ((:) '\x03' ((:) '&' ((:) '\xa8' ((:) '\x05' ((:) '\xbb' ((:)
        '\xef' ((:) '\xd4' ((:) '\x80' ((:) 'V' ((:) '\xc8' ((:) '\xc1' ((:)
        '!' ((:) '\xbd' ((:) '\xb8'
        ([]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Builtin DefaultUniByteString)))
    (Builtin Bls12_381_G2_compress)) ([])) (Let NonRec ((:) (TermBind Strict
    (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))
    (Ty_Fun (Ty_Builtin DefaultUniBLS12_381_G2_Element) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Builtin
    DefaultUniBLS12_381_G2_Element)))) (Builtin Bls12_381_G2_add)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniBLS12_381_G1_Element)))
    (Builtin Bls12_381_G1_uncompress)) ([])) (Let NonRec ((:) (TermBind
    Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniBLS12_381_G1_Element)
    (Ty_Builtin DefaultUniBLS12_381_G1_Element)))) (Builtin
    Bls12_381_G1_scalarMul)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G1_Element) (Ty_Builtin
    DefaultUniBLS12_381_G1_Element))) (Builtin Bls12_381_G1_neg)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniBLS12_381_G1_Element)))) (Builtin
    Bls12_381_G1_hashToGroup)) ([])) (Let NonRec ((:) (TermBind Strict
    (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))
    (Ty_Fun (Ty_Builtin DefaultUniBLS12_381_G1_Element) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G1_Element) (Ty_Builtin DefaultUniBool)))) (Builtin
    Bls12_381_G1_equal)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1)))))) (Ty_Builtin DefaultUniByteString))
    (Constant0
    (some (ValueOf DefaultUniByteString
      (unsafeCoerce ((:) '\xc0' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:)
        '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00' ((:) '\x00'
        ([])))))))))))))))))))))))))))))))))))))))))))))))))))))) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))))))
    (Ty_Builtin DefaultUniByteString)) (Constant0
    (some (ValueOf DefaultUniByteString
      (unsafeCoerce ((:) '\x97' ((:) '\xf1' ((:) '\xd3' ((:) '\xa7' ((:) '1'
        ((:) '\x97' ((:) '\xd7' ((:) '\x94' ((:) '&' ((:) '\x95' ((:) 'c'
        ((:) '\x8c' ((:) 'O' ((:) '\xa9' ((:) '\xac' ((:) '\x0f' ((:) '\xc3'
        ((:) 'h' ((:) '\x8c' ((:) 'O' ((:) '\x97' ((:) 't' ((:) '\xb9' ((:)
        '\x05' ((:) '\xa1' ((:) 'N' ((:) ':' ((:) '?' ((:) '\x17' ((:) '\x1b'
        ((:) '\xac' ((:) 'X' ((:) 'l' ((:) 'U' ((:) '\xe8' ((:) '?' ((:)
        '\xf9' ((:) 'z' ((:) '\x1a' ((:) '\xef' ((:) '\xfb' ((:) ':' ((:)
        '\xf0' ((:) '\n' ((:) '\xdb' ((:) '"' ((:) '\xc6' ((:) '\xbb'
        ([])))))))))))))))))))))))))))))))))))))))))))))))))))))) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G1_Element) (Ty_Builtin DefaultUniByteString)))
    (Builtin Bls12_381_G1_compress)) ([])) (Let NonRec ((:) (TermBind Strict
    (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))
    (Ty_Fun (Ty_Builtin DefaultUniBLS12_381_G1_Element) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G1_Element) (Ty_Builtin
    DefaultUniBLS12_381_G1_Element)))) (Builtin Bls12_381_G1_add)) ([])) (Let
    NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) 1))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))) (Builtin
    Blake2b_256)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))) (Builtin
    Blake2b_224)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))) (Ty_Fun (Ty_Builtin
    DefaultUniString) (Ty_Fun (Ty_Builtin DefaultUniString) (Ty_Builtin
    DefaultUniString)))) (Builtin AppendString)) ([])) (Let NonRec ((:)
    (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString)))) (Builtin
    AppendByteString)) ([])) (Let NonRec ((:) (TermBind Strict (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBool) (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniByteString)))))
    (Builtin AndByteString)) ([])) (Let NonRec ((:) (TypeBind (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))) Kind_Base)
    (Ty_Builtin DefaultUniUnit)) ([])) (Let NonRec ((:) (TypeBind (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))
    Kind_Base) (Ty_Builtin DefaultUniString)) ([])) (Let NonRec ((:)
    (TypeBind (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))) (Kind_Arrow Kind_Base
    (Kind_Arrow Kind_Base Kind_Base))) (Ty_Builtin DefaultUniProtoPair))
    ([])) (Let NonRec ((:) (TypeBind (TyVarDecl (show_Z 0) Kind_Base)
    (Ty_Builtin DefaultUniByteString)) ([])) (Let NonRec ((:) (TypeBind
    (TyVarDecl (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) 1))) Kind_Base)
    (Ty_Builtin DefaultUniBool)) ([])) (Let NonRec ((:) (TypeBind (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1)))))
    Kind_Base) (Ty_Builtin DefaultUniBLS12_381_MlResult)) ([])) (Let NonRec
    ((:) (TypeBind (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))) Kind_Base)
    (Ty_Builtin DefaultUniBLS12_381_G2_Element)) ([])) (Let NonRec ((:)
    (TypeBind (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))) Kind_Base) (Ty_Builtin
    DefaultUniBLS12_381_G1_Element)) ([])) (TyInst (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      1)))))))))) (Ty_Builtin
    DefaultUniInteger))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

ast_ty :: Prelude.Maybe Ty
ast_ty =
  type_check ([]) ([]) ast


small :: Term
small = Let NonRec ((:) (TermBind Strict (VarDecl
    "x" (Ty_Fun (Ty_Builtin DefaultUniBool) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniByteString))))) (Builtin XorByteString)) ([])) (Var "x")

term_ty_comp :: Term 
term_ty_comp = LamAbs "x" (Ty_App (Ty_Lam "A" Kind_Base (Ty_Var "A")) (Ty_Builtin DefaultUniInteger)) (Var "x")

main :: Prelude.IO ()
main = Prelude.putStrLn "Hello, world!"

tySOP :: () -> (([]) (([]) Ty)) -> Ty
tySOP _ _ =
  Ty_Var ""

maybeFun_compiled_simple :: Term
maybeFun_compiled_simple =
  Let NonRec ((:) (DatatypeBind (Datatype (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) (Kind_Arrow Kind_Base
    Kind_Base)) ((:) (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) Kind_Base) ([]))
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) ((:) (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))
    (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_App (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))))))) ((:) (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) (Ty_App (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))))) ([]))))) ([])) 
      (LamAbs "x" (Ty_Builtin DefaultUniInteger) (Var "x"))

maybeFun_compiled :: Term
maybeFun_compiled =
  Let NonRec ((:) (DatatypeBind (Datatype (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) (Kind_Arrow Kind_Base
    Kind_Base)) ((:) (TyVarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) Kind_Base) ([]))
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) ((:) (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))
    (Ty_Fun (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_App (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))))))) ((:) (VarDecl
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) (Ty_App (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))))) ([]))))) ([]))


    (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))
    (Ty_App (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Builtin
    DefaultUniInteger)) 
    
    (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) (Ty_App (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Builtin
    DefaultUniInteger)) 
    
    
    (TyInst (Apply (Apply (TyInst (Apply (TyInst (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Builtin
    DefaultUniInteger)) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))))
    (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) Kind_Base (Ty_App
    (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Builtin
    DefaultUniInteger)))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) (Ty_Builtin
    DefaultUniInteger) (TyAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))
    Kind_Base (TyInst (Apply (Apply (TyInst (Apply (TyInst (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Builtin
    DefaultUniInteger)) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) Kind_Base (Ty_App
    (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Builtin
    DefaultUniInteger)))) (LamAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) (Ty_Builtin
    DefaultUniInteger) (TyAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) Kind_Base (Apply
    (TyInst (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))))
    (Ty_Builtin DefaultUniInteger)) (Apply (Apply (Builtin AddInteger) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))))) (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))))))))) (TyAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) Kind_Base (TyInst (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Builtin
    DefaultUniInteger)))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))
    Kind_Base (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))))))))
    (TyAbs
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) Kind_Base (TyInst (Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))))) (Ty_Builtin
    DefaultUniInteger)))) (Ty_Forall
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))) Kind_Base (Ty_Var
    (show_Z ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))))))
      ))
