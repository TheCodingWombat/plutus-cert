
Require Import PlutusCert.Util.List.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import PlutusIR Util.

Reserved Notation "'|-*_uni' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_kind_uni : DefaultUni -> kind -> Prop :=
  | K_DefaultUniInteger :
      |-*_uni DefaultUniInteger : Kind_Base
  | K_DefaultUniByteString :
      |-*_uni DefaultUniByteString : Kind_Base
  | K_DefaultUniString :
      |-*_uni DefaultUniString : Kind_Base
  | K_DefaultUniUnit :
      |-*_uni DefaultUniUnit : Kind_Base
  | K_DefaultUniBool :
      |-*_uni DefaultUniBool : Kind_Base
  | K_DefaultUniData :
      |-*_uni DefaultUniData : Kind_Base
  | K_DefaultUniBLS12_381_G1_Element :
      |-*_uni DefaultUniBLS12_381_G1_Element : Kind_Base
  | K_DefaultUniBLS12_381_G2_Element :
      |-*_uni DefaultUniBLS12_381_G2_Element : Kind_Base
  | K_DefaultUniBLS12_381_MlResult :
      |-*_uni DefaultUniBLS12_381_MlResult : Kind_Base
  | K_DefaultUniApply k k' t t':
      |-*_uni t : (Kind_Arrow k k') ->
      |-*_uni t' : k ->
      |-*_uni (DefaultUniApply t t') : k'
  | K_DefaultUniProtoPair :
      |-*_uni DefaultUniProtoPair : (Kind_Arrow Kind_Base (Kind_Arrow Kind_Base Kind_Base))
  | K_DefaultUniProtoList :
      |-*_uni DefaultUniProtoList : (Kind_Arrow Kind_Base Kind_Base)
  where "'|-*_uni' T ':' K" := (has_kind_uni T K)
.


(* Example ill-kinded:
nil |-* TyApp (Lam bX Kind_Base "bX") (Lam bY Kind_Base "bY")

So then: nil |-* (Lam bY Kind_Base "bY") : K1a -> K1b
(bY, Kind_Base) |-* "bY" : Kind_Base = K1b
also K1a = K1b = Kind_Base
Hence K1 := Kind_Base -> Kind_Base

lam bX Kind_Base "bX" : (KB -> KB) -> K2 ?
No, because it is KB -> KB in total.
No way to unify (KB -> KB) -> K2 with KB -> KB

*)


(** Kinding of types *)
Reserved Notation "Δ '|-*' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_kind : list (binderTyname * kind) -> ty -> kind -> Prop :=
  | K_Var : forall Δ X K,
      lookup X Δ = Some K ->
      Δ |-* (Ty_Var X) : K
  | K_Fun : forall Δ T1 T2,
      Δ |-* T1 : Kind_Base ->
      Δ |-* T2 : Kind_Base ->
      Δ |-* (Ty_Fun T1 T2) : Kind_Base
  | K_IFix  : forall Δ F T K,
      Δ |-* T : K ->
      Δ |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      Δ |-* (Ty_IFix F T) : Kind_Base
  | K_Forall : forall Δ X K T,
      ((X, K) :: Δ) |-* T : Kind_Base ->
      Δ |-* (Ty_Forall X K T) : Kind_Base
  | K_Builtin : forall Δ T,
      |-*_uni T : Kind_Base ->
      Δ |-* (Ty_Builtin T) : Kind_Base
  | K_Lam : forall Δ X K1 T K2,
      ((X, K1) :: Δ) |-* T : K2 ->
      Δ |-* (Ty_Lam X K1 T) : (Kind_Arrow K1 K2)
  | K_App : forall Δ T1 T2 K1 K2,
      Δ |-* T1 : (Kind_Arrow K1 K2) ->
      Δ |-* T2 : K1 ->
      Δ |-* (Ty_App T1 T2) : K2
  | K_SOP : forall Δ Tss,
      Forall (Forall (fun T => has_kind Δ T Kind_Base)) Tss ->
      Δ |-* (Ty_SOP Tss) : Kind_Base
where "Δ '|-*' T ':' K" := (has_kind Δ T K).

Section has_kind__ind.

  Unset Implicit Arguments.

  Variable (P : list (binderTyname * kind) -> ty -> kind -> Prop).

  Context
    (H_Var : forall Δ X K,
        lookup X Δ = Some K ->
        P Δ (Ty_Var X) K)
    (H_Fun : forall Δ T1 T2,
        P Δ T1 Kind_Base ->
        P Δ T2 Kind_Base ->
        P Δ (Ty_Fun T1 T2) Kind_Base)
    (H_IFix : forall Δ F T K,
        P Δ T K ->
        P Δ F (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
        P Δ (Ty_IFix F T) Kind_Base)
    (H_Forall : forall Δ X K T,
        P ((X, K) :: Δ) T Kind_Base ->
        P Δ (Ty_Forall X K T) Kind_Base)
    (H_Builtin : forall Δ T,
        |-*_uni T : Kind_Base ->
        P Δ (Ty_Builtin T) Kind_Base)
    (H_Lam : forall Δ X K1 T K2,
        P ((X, K1) :: Δ) T K2 ->
        P Δ (Ty_Lam X K1 T) (Kind_Arrow K1 K2))
    (H_App : forall Δ T1 T2 K1 K2,
        P Δ T1 (Kind_Arrow K1 K2) ->
        P Δ T2 K1 ->
        P Δ (Ty_App T1 T2) K2)
    (H_SOP : forall Δ Tss,
        Forall (Forall (fun T => P Δ T Kind_Base)) Tss ->
        P Δ (Ty_SOP Tss) Kind_Base).

  Fixpoint has_kind__ind Δ T K (HK : Δ |-* T : K) : P Δ T K :=
    match HK with
    | K_Var Δ X K Hlookup => H_Var Δ X K Hlookup
    | K_Fun Δ T1 T2 HK1 HK2 =>
        H_Fun Δ T1 T2 (has_kind__ind Δ T1 Kind_Base HK1)
                     (has_kind__ind Δ T2 Kind_Base HK2)
    | K_IFix Δ F T K HKT HKF =>
        H_IFix Δ F T K (has_kind__ind Δ T K HKT)
                       (has_kind__ind Δ F _ HKF)
    | K_Forall Δ X K T HKT =>
        H_Forall Δ X K T (has_kind__ind ((X, K) :: Δ) T Kind_Base HKT)
    | K_Builtin Δ T HUni =>
        H_Builtin Δ T HUni
    | K_Lam Δ X K1 T K2 HKT =>
        H_Lam Δ X K1 T K2 (has_kind__ind ((X, K1) :: Δ) T K2 HKT)
    | K_App Δ T1 T2 K1 K2 HK1 HK2 =>
        H_App Δ T1 T2 K1 K2 (has_kind__ind Δ T1 _ HK1)
                             (has_kind__ind Δ T2 _ HK2)
    | K_SOP Δ Tss HForall =>
        H_SOP Δ Tss
          (let fix forall_ts ts (Hts : Forall (fun T => has_kind Δ T Kind_Base) ts) :
               Forall (fun T => P Δ T Kind_Base) ts :=
             match Hts with
             | Forall_nil _ => Forall_nil _
             | @Forall_cons _ _ t ts' Ht Hts' =>
                 @Forall_cons _ _ t ts' (has_kind__ind Δ t Kind_Base Ht) (forall_ts ts' Hts')
             end in
           let fix forall_tss tss (Htss : Forall (Forall (fun T => has_kind Δ T Kind_Base)) tss) :
               Forall (Forall (fun T => P Δ T Kind_Base)) tss :=
             match Htss with
             | Forall_nil _ => Forall_nil _
             | @Forall_cons _ _ ts tss' Hts Htss' =>
                 @Forall_cons _ _ ts tss' (forall_ts ts Hts) (forall_tss tss' Htss')
             end in
           forall_tss Tss HForall)
    end.

End has_kind__ind.

Local Open Scope string_scope.

(* TODO: there is probably a higher order thing to create stuff like this *)
Inductive map_wk : list (string * ty * list (string * kind)) -> Prop :=
  | MW_nil :
      map_wk nil
  | MW_cons : forall X Δ T (xs : list (string * ty * list (string * kind))) K,
      map_wk xs ->
      has_kind Δ T K ->
      map_wk ((X, T, Δ) :: xs).

(* TODO: Is this what we usually call app? *)
Lemma map_wk_app : forall xs ys,
  map_wk xs ->
  map_wk ys ->
  map_wk (xs ++ ys).
Proof.
    intros xs ys H_xs.
    induction H_xs; intros H_ys; try econstructor; eauto.
Qed.

(** Kinding of types *)
Reserved Notation "Δ '|-*s' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_kind_set : list (binderTyname * kind) -> ty -> kind -> Set :=
  | K_Var_set : forall Δ X K,
      lookup X Δ = Some K ->
      Δ |-*s (Ty_Var X) : K
  | K_Fun_set : forall Δ T1 T2,
      Δ |-*s T1 : Kind_Base ->
      Δ |-*s T2 : Kind_Base ->
      Δ |-*s (Ty_Fun T1 T2) : Kind_Base
  | K_IFix_set  : forall Δ F T K,
      Δ |-*s T : K ->
      Δ |-*s F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      Δ |-*s (Ty_IFix F T) : Kind_Base
  | K_Forall_set : forall Δ X K T,
      ((X, K) :: Δ) |-*s T : Kind_Base ->
      Δ |-*s (Ty_Forall X K T) : Kind_Base
  | K_Builtin_set : forall Δ T,
      |-*_uni T : Kind_Base ->
      Δ |-*s (Ty_Builtin T) : Kind_Base
  | K_Lam_set : forall Δ X K1 T K2,
      ((X, K1) :: Δ) |-*s T : K2 ->
      Δ |-*s (Ty_Lam X K1 T) : (Kind_Arrow K1 K2)
  | K_App_set : forall Δ T1 T2 K1 K2,
      Δ |-*s T1 : (Kind_Arrow K1 K2) ->
      Δ |-*s T2 : K1 ->
      Δ |-*s (Ty_App T1 T2) : K2
  | K_SOP_set : forall Δ Tss,
      ForallT (ForallT (fun T => has_kind_set Δ T Kind_Base)) Tss ->
      Δ |-*s (Ty_SOP Tss) : Kind_Base
where "Δ '|-*s' T ':' K" := (has_kind_set Δ T K).

Section has_kind_set__ind.

  Unset Implicit Arguments.

  Variable (P : list (binderTyname * kind) -> ty -> kind -> Set).

  (* The following are the induction hypotheses for each constructor of has_kind_set *)
  (* They are used to prove the inductive step in has_kind_set__ind *)

Context
  (H_Var_set :
     forall Δ X K,
       lookup X Δ = Some K ->
       P Δ (Ty_Var X) K)
  (H_Fun_set :
     forall Δ T1 T2,
       P Δ T1 Kind_Base ->
       P Δ T2 Kind_Base ->
       P Δ (Ty_Fun T1 T2) Kind_Base)
  (H_IFix_set :
     forall Δ F T K,
       P Δ T K ->
       P Δ F (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
       P Δ (Ty_IFix F T) Kind_Base)
  (H_Forall_set :
     forall Δ X K T,
       P ((X, K) :: Δ) T Kind_Base ->
       P Δ (Ty_Forall X K T) Kind_Base)
  (H_Builtin_set :
     forall Δ T,
       |-*_uni T : Kind_Base ->
       P Δ (Ty_Builtin T) Kind_Base)
  (H_Lam_set :
     forall Δ X K1 T K2,
       P ((X, K1) :: Δ) T K2 ->
       P Δ (Ty_Lam X K1 T) (Kind_Arrow K1 K2))
  (H_App_set :
     forall Δ T1 T2 K1 K2,
       P Δ T1 (Kind_Arrow K1 K2) ->
       P Δ T2 K1 ->
       P Δ (Ty_App T1 T2) K2)
  (H_SOP_set :
     forall Δ Tss,
       ForallT (ForallT (fun T => P Δ T Kind_Base)) Tss ->
       P Δ (Ty_SOP Tss) Kind_Base).

Fixpoint has_kind_set__ind
         (Δ : list (binderTyname * kind)) (T : ty) (K : kind)
         (HK : has_kind_set Δ T K) : P Δ T K :=
  match HK with
  | K_Var_set Δ X K Hlookup =>
      H_Var_set Δ X K Hlookup

  | K_Fun_set Δ T1 T2 HK1 HK2 =>
      H_Fun_set Δ T1 T2
        (has_kind_set__ind Δ T1 Kind_Base HK1)
        (has_kind_set__ind Δ T2 Kind_Base HK2)

  | K_IFix_set Δ F T K HKT HKF =>
      H_IFix_set Δ F T K
        (has_kind_set__ind Δ T K HKT)
        (has_kind_set__ind Δ F (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) HKF)

  | K_Forall_set Δ X K T HKT =>
      H_Forall_set Δ X K T
        (has_kind_set__ind ((X, K) :: Δ) T Kind_Base HKT)

  | K_Builtin_set Δ T Huni =>
      H_Builtin_set Δ T Huni

  | K_Lam_set Δ X K1 T K2 HKT =>
      H_Lam_set Δ X K1 T K2
        (has_kind_set__ind ((X, K1) :: Δ) T K2 HKT)

  | K_App_set Δ T1 T2 K1 K2 HK1 HK2 =>
      H_App_set Δ T1 T2 K1 K2
        (has_kind_set__ind Δ T1 (Kind_Arrow K1 K2) HK1)
        (has_kind_set__ind Δ T2 K1 HK2)

  | K_SOP_set Δ Tss HForallT =>
      H_SOP_set Δ Tss
        (let fix map_outer (tss : list (list ty))
                           (H : ForallT (ForallT (fun T => has_kind_set Δ T Kind_Base)) tss)
                           : ForallT (ForallT (fun T => P Δ T Kind_Base)) tss :=
           match H with
           | ForallT_nil  => ForallT_nil
           | ForallT_cons Hts Hrest =>
               let fix map_inner (ts : list ty)
                                 (Hts : ForallT (fun T => has_kind_set Δ T Kind_Base) ts)
                                 : ForallT (fun T => P Δ T Kind_Base) ts :=
                   match Hts with
                   | ForallT_nil => ForallT_nil
                   | ForallT_cons Ht Hts' =>
                       ForallT_cons
                         (has_kind_set__ind Δ _ Kind_Base Ht)
                         (map_inner _ Hts')
                   end
               in
               ForallT_cons 
                 (map_inner _ Hts)
                 (map_outer _ Hrest)
           end
         in map_outer Tss HForallT)
  end.

End has_kind_set__ind.