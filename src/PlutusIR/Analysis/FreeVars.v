Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Ascii.

From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import  PlutusIR.Folds.
From PlutusCert Require Import  Analysis.BoundVars.
From PlutusCert Require Import  Util.
From PlutusCert Require Import  Util.List.

(* Set Implicit Arguments. *)

Module Ty.

  Function ftv (T : ty) : list string :=
    match T with
    | Ty_Var X =>
        [X]
    | Ty_Fun T1 T2 =>
        ftv T1 ++ ftv T2
    | Ty_IFix F T =>
        ftv F ++ ftv T
    | Ty_Forall X K T' =>
        remove string_dec X (ftv T')
    | Ty_Builtin u =>
        []
    | Ty_Lam X K1 T' =>
        remove string_dec X (ftv T')
    | Ty_App T1 T2 =>
        ftv T1 ++ ftv T2
    end.

End Ty.


Module Term.

  Section Bindings.

    (* It becomes a parameter to both fvbs and the generated
       fvbs_equation *)
    Context (fvb : recursivity -> binding -> list string).

    Function fvbs  rec (bs : list binding) : list string :=
      match bs with
       | nil     => []
        | b :: bs =>
           match rec with
             | Rec    =>
                 (fvb Rec b ++ fvbs Rec bs) \ (bvbs (b :: bs))
             | NonRec =>
                 fvb NonRec b ++ (fvbs NonRec bs \ (bvb b))
           end
      end.

  End Bindings.

  Function fv (t : term) : list string :=
    match t with
     | Let rec bs t    => fvbs fvb rec bs ++ remove_many string_dec (bvbs bs) (fv t)
     | LamAbs n ty t   => remove string_dec n (fv t)
     | Var n           => [n]
     | TyAbs n k t     => fv t
     | Apply s t       => fv s ++ fv t
     | TyInst t ty     => fv t
     | IWrap ty1 ty2 t => fv t
     | Unwrap t        => fv t
     | Error ty        => []
     | Constant v      => []
     | Builtin f       => []
     | Constr i ts     => concat (map fv ts)
     | Case t ts       => fv t ++ concat (map fv ts)
   end

  with fvb rec (b : binding) : list string :=
    match b with
      | TermBind _ (VarDecl v _) t => match rec with
        | Rec    => remove string_dec v (fv t)
        | NonRec => fv t
        end
      | _        => []
    end
    .

  (* Write by hand, because somehow it isn't generated for fvb *)
  Lemma fvb_equation rec (b : binding) :
    fvb rec b =
    match b with
      | TermBind _ (VarDecl v _) t => match rec with
        | Rec    => remove string_dec v (fv t)
        | NonRec => fv t
        end
      | _        => []
    end
    .
  Proof.
    destruct b; destruct rec;
    reflexivity.
  Qed.


  Section Bindings.
  Context (ftvb : recursivity -> binding -> list string).

  Function ftvbs rec bs : list string :=
    match bs with
      | nil => []
      | b :: bs => match rec with
        | Rec =>
             remove_many string_dec (btvbs (b :: bs)) (ftvb Rec b)
          ++ remove_many string_dec (btvbs (b :: bs)) (ftvbs NonRec bs)
        | NonRec =>
             ftvb NonRec b
          ++ remove_many string_dec (btvb b) (ftvbs NonRec bs)
        end
    end.

  End Bindings.


  (*
  Lemma ftvbs_NonRec_cons ftvb b bs :
     ftvbs ftvb NonRec (b :: bs)
   = ftvb NonRec b ++ remove_many tyvar_dec (btvb b) (ftvbs ftvb NonRec bs).
  Proof.
    reflexivity.
  Qed.

  Lemma ftvbs_Rec_cons ftvb b bs :
     ftvbs ftvb Rec (b :: bs)
   = ftvb NonRec b ++ remove_many tyvar_dec (btvbs (b :: bs)) (ftvbs ftvb Rec bs).
  Proof.
    simpl.
    reflexivity.
  Qed.
  *)

  Definition ftvc (c : vdecl) : list string :=
    match c with
      | VarDecl _ τ => Ty.ftv τ
    end.

  Function ftv (t : term) : list string :=
   match t with
     | Let rec bs t    => ftvbs ftvb rec bs ++ remove_many string_dec (btvbs bs) (ftv t)
     | LamAbs n τ t    => Ty.ftv τ ++ ftv t
     | Var n           => []
     | TyAbs α k t     => remove string_dec α (ftv t)
     | Apply s t       => ftv s ++ ftv t
     | TyInst t τ      => Ty.ftv τ ++ ftv t
     | IWrap τ1 τ2 t   => Ty.ftv τ1 ++ Ty.ftv τ2 ++ ftv t
     | Unwrap t        => ftv t
     | Error τ         => Ty.ftv τ
     | Constant v      => []
     | Builtin f       => []
     | (Constr i ts)   => concat (map ftv ts)
     | (Case t ts)    => ftv t ++ concat (map ftv ts)
     end

  with ftvb rec (b : binding) : list string :=
    match b with
      | TermBind s (VarDecl _ τ) t => Ty.ftv τ ++ ftv t
      | TypeBind (TyVarDecl α k) τ  => Ty.ftv τ
      | DatatypeBind (Datatype (TyVarDecl α _) params m cs) => concat (map ftvc cs)
    end
    .

  Lemma ftvb_equation rec b :
    ftvb rec b =
    match b with
      | TermBind s (VarDecl _ τ) t => Ty.ftv τ ++ ftv t
      | TypeBind (TyVarDecl α k) τ => Ty.ftv τ
      | DatatypeBind (Datatype (TyVarDecl α _) params m cs) => concat (map ftvc cs)
    end.
  Proof.
    destruct rec, b.
    all: reflexivity.
  Qed.

End Term.
