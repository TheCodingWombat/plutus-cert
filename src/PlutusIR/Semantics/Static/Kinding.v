Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
Require Import Coq.Bool.Bool.

Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Import List.
Import ListNotations.

Import PlutusNotations.

Fixpoint eqb_kind (K1 K2:kind) : bool :=
    match K1,K2 with
    | Kind_Base, Kind_Base => true
    | Kind_Arrow K11 K12, Kind_Arrow K21 K22 =>
        andb (eqb_kind K11 K21) (eqb_kind K12 K22)
    | _, _ => false
    end.

(* Based on Software Foundation's eqb_type_refl *)
Lemma eqb_kind_refl : forall kind,
    eqb_kind kind kind = true.
Proof.
    intros kind.
    induction kind.
    - simpl. reflexivity.
    - simpl. rewrite -> IHkind1. rewrite -> IHkind2. simpl. reflexivity.
Qed.

(* Based on Software Foundation's eqb_type_eq*)
Lemma eqb_kind_eq : forall K1 K2,
    eqb_kind K1 K2 = true -> K1 = K2.
Proof with auto.
    intros K1. induction K1; intros K2 HBeq; destruct K2; inversion HBeq.
    - reflexivity.
    - rewrite andb_true_iff in H0. 
      inversion H0 as [Hbeq1 Hbeq2].
      apply IHK1_1 in Hbeq1.
      apply IHK1_2 in Hbeq2.
      subst...
Qed.

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
      |-*_uni DefaultUniProtoPair : (Kind_Arrow Kind_Base Kind_Base)
  | K_DefaultUniProtoList :
      |-*_uni DefaultUniProtoList : (Kind_Arrow Kind_Base Kind_Base)
  where "'|-*_uni' T ':' K" := (has_kind_uni T K)
.

Fixpoint kind_check_default_uni (d : DefaultUni) : option kind :=
  match d with
  | DefaultUniInteger => Some Kind_Base
  | DefaultUniByteString => Some Kind_Base
  | DefaultUniString => Some Kind_Base
  | DefaultUniUnit => Some Kind_Base
  | DefaultUniBool => Some Kind_Base
  | DefaultUniData => Some Kind_Base
  | DefaultUniBLS12_381_G1_Element => Some Kind_Base
  | DefaultUniBLS12_381_G2_Element => Some Kind_Base
  | DefaultUniBLS12_381_MlResult => Some Kind_Base
  | DefaultUniApply t t' =>
      match (kind_check_default_uni t, kind_check_default_uni t') with
      | (Some (Kind_Arrow k k'), Some k'') => if eqb_kind k'' k then Some k' else None
      | _ => None
      end
  | DefaultUniProtoPair => Some (Kind_Arrow Kind_Base Kind_Base)
  | DefaultUniProtoList => Some (Kind_Arrow Kind_Base Kind_Base)
  end.

Lemma kind_checking_default_uni_sound : forall d k,
    kind_check_default_uni d = Some k -> |-*_uni d : k.
Proof.
  intros d k H. generalize dependent k.
  induction d; intros k H; inversion H.
  - apply K_DefaultUniInteger.
  - apply K_DefaultUniByteString.
  - apply K_DefaultUniString.
  - apply K_DefaultUniUnit.
  - apply K_DefaultUniBool.
  (* TODO: has_kind_uni does not have same order of constructors as DefaultUni, really confusing*)
  - apply K_DefaultUniProtoList.
  - apply K_DefaultUniProtoPair.
  - apply K_DefaultUniData.
  - apply K_DefaultUniBLS12_381_G1_Element.
  - apply K_DefaultUniBLS12_381_G2_Element.
  - apply K_DefaultUniBLS12_381_MlResult.
  - destruct (kind_check_default_uni d1) eqn:Hd1; [|discriminate].
    destruct k0 eqn:Hk0; [discriminate|].
    destruct (kind_check_default_uni d2) eqn:Hd2; [|discriminate].
    destruct (eqb_kind k1 k1_1) eqn:Heqb; [|discriminate].
    apply eqb_kind_eq in Heqb.
    subst.
    apply K_DefaultUniApply with (k := k1_1).
    + apply IHd1.
      inversion H1.
      reflexivity.
    + apply IHd2.
      inversion H1.
      reflexivity. 
Qed.

Lemma kind_checking_default_uni_complete : forall d k,
    |-*_uni d : k -> kind_check_default_uni d = Some k.
Proof.
  intros d k H.
  induction H; simpl; try reflexivity.
  - rewrite -> IHhas_kind_uni1.
    rewrite -> IHhas_kind_uni2.
    rewrite eqb_kind_refl.
    reflexivity.
Qed.
      

Definition extractDefaultUni {d : DefaultUni} (t : typeIn d) : DefaultUni :=
  match t with
  | TypeIn _ => d
  end.

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
  | K_Builtin : forall Δ u K,
      |-*_uni u : K ->
      Δ |-* (Ty_Builtin (Some' (TypeIn u))) : K
  | K_Lam : forall Δ X K1 T K2,
      ((X, K1) :: Δ) |-* T : K2 ->
      Δ |-* (Ty_Lam X K1 T) : (Kind_Arrow K1 K2)
  | K_App : forall Δ T1 T2 K1 K2,
      Δ |-* T1 : (Kind_Arrow K1 K2) ->
      Δ |-* T2 : K1 ->
      Δ |-* (Ty_App T1 T2) : K2
where "Δ '|-*' T ':' K" := (has_kind Δ T K).

Fixpoint kind_check (Delta : list (binderTyname * kind)) (ty : ty) : (option kind) :=
    match ty with
    | Ty_Var X => (* Based on Software Foundations and has_kind *)
        lookup X Delta
    | Ty_Fun T1 T2 => (* TODO: I don't understand what this datatype does*)
        match (kind_check Delta T1, kind_check Delta T2) with
        | (Some Kind_Base, Some Kind_Base) => Some Kind_Base
        | (_, _) => None
        end
    | Ty_IFix F T => (* Note: Purely based on structure of has_kind *)
        match kind_check Delta T with
        | Some K => match kind_check Delta F with
            | Some (Kind_Arrow (Kind_Arrow K1 Kind_Base) (Kind_Arrow K2 Kind_Base)) =>
                if andb (eqb_kind K K1) (eqb_kind K K2) then Some Kind_Base else None
            | _ => None
            end
        | _ => None
        end
    | Ty_Forall X K T =>
        match kind_check ((X, K) :: Delta) T with
        | Some Kind_Base => Some Kind_Base
        | _ => None
        end
    | Ty_Builtin (Some' typeIn) =>
        let d := extractDefaultUni typeIn in
        kind_check_default_uni d
    | Ty_Lam X K1 T => (* Note: Copied from Software Foundations *)
        match kind_check ((X, K1) :: Delta) T with
        | Some K2 => Some (Kind_Arrow K1 K2)
        | _ => None
        end
    | Ty_App T1 T2 => 
        match (kind_check Delta T1, kind_check Delta T2) with
        | (Some (Kind_Arrow K11 K2), Some K12) =>
            if eqb_kind K11 K12 then Some K2 else None
        | (_, _) => None
        end
    end.

Theorem kind_checking_sound : forall Delta ty kind,
    kind_check Delta ty = Some kind -> has_kind Delta ty kind.
Proof.
    intros Delta ty. generalize dependent Delta.
    induction ty; intros Delta kind Htc; inversion Htc.
    - (* Var *) 
      destruct (lookup t Delta) eqn:H; [|discriminate].
      apply K_Var.
      rewrite H0 in H.
      apply H.
    - (* Ty_Fun *) 
      assert (kind = Kind_Base) as Hkind_base.
      {
        destruct (kind_check Delta ty1); [|discriminate].
        destruct k; [|discriminate].
        destruct (kind_check Delta ty2); [|discriminate].
        destruct k; [|discriminate].
        inversion H0.
        reflexivity.
      }
      subst kind.
      apply K_Fun.
      + apply IHty1.
        destruct (kind_check Delta ty1) eqn:Hkc; [|discriminate].
        destruct k; [|discriminate].
        reflexivity.        
      + apply IHty2.
        destruct (kind_check Delta ty1); [|discriminate].
        destruct k; [|discriminate].
        destruct (kind_check Delta ty2); [|discriminate].
        destruct k; [|discriminate].
        reflexivity.
    - (* Ty_IFix *) (* TODO: How do I make ty1 and ty2 resemble F and T as in the formualtion of has_kind?*)
      assert (kind = Kind_Base) as Hkind_base.
      {
        (* TODO: Code duplication with after apply IHty1*)
        destruct (kind_check Delta ty2); [|discriminate].
        destruct (kind_check Delta ty1); [|discriminate].
        destruct k0; [discriminate|].
        destruct k0_1; [discriminate|].
        destruct k0_1_2; [|discriminate].
        destruct k0_2; [discriminate|].
        destruct k0_2_2; [|discriminate].
        destruct (eqb_kind k k0_1_1 && eqb_kind k k0_2_1); [|discriminate].
        inversion H0.
        reflexivity.
      }
      subst kind.
      remember (kind_check Delta ty2) as K.
      destruct K as [k|]; [|discriminate].
      apply K_IFix with (K := k). 
      + apply IHty2.
        rewrite HeqK.
        reflexivity. 
      + apply IHty1.
        destruct (kind_check Delta ty1); [|discriminate].
        destruct k0; [discriminate|].
        destruct k0_1; [discriminate|].
        destruct k0_1_2; [|discriminate].
        destruct k0_2; [discriminate|].
        destruct k0_2_2; [|discriminate].
        destruct (eqb_kind k k0_1_1 && eqb_kind k k0_2_1) eqn:eqbs; [|discriminate].
        apply andb_true_iff in eqbs.
        destruct eqbs as [eqb1 eqb2].
        apply eqb_kind_eq in eqb1.
        apply eqb_kind_eq in eqb2.
        subst...
        reflexivity.
    - (* Ty_Forall *)
      assert (kind = Kind_Base) as Hkind_base.
      {
        destruct (kind_check ((b, k) :: Delta) ty); [|discriminate].
        destruct k0; [|discriminate].
        inversion H0.
        reflexivity.
      }
      rewrite Hkind_base. 
      (* The result of the K_Forall case matches and thus we can apply it!*)
      apply K_Forall.
      (* Now this is in the form of our induction hypothesis*)
      apply IHty.
      (* Final steps, use H0, which derives from the definition of kind_check*)
      destruct (kind_check ((b, k) :: Delta) ty) as [k0|]; [|discriminate].
      destruct k0; [|discriminate];
      rewrite -> H0.
      reflexivity.
    - (* Ty_Builtin *)
      destruct s as [u typeIn] eqn:Hs.
      rewrite -> typeIn.
      apply K_Builtin.
      rewrite typeIn in H0.
      simpl in H0.
      apply kind_checking_default_uni_sound in H0.
      assumption.
    - (* Ty_Lam *)
      (* prove that kind = Kind_Arrow _ _*)
      destruct (kind_check ((b, k) :: Delta) ty) eqn:Hkc; [|discriminate].
      inversion H0.
      apply K_Lam. (* Apply has_kind structure*)
      apply IHty.
      apply Hkc. (* Apply kind_check structure*)
    - (* Ty_App *) 
      remember (kind_check Delta ty2) as K1.
      destruct K1 as [k1|].
      + apply K_App with (K1 := k1).  
        * apply IHty1.
          destruct (kind_check Delta ty1); [|discriminate].
          destruct k; [discriminate|].
          destruct (eqb_kind k2 k1) eqn:eqb ; [|discriminate].
          inversion H0.
          apply eqb_kind_eq in eqb.
          rewrite eqb.
          reflexivity.
        * apply IHty2.
          rewrite HeqK1.
          reflexivity. 
      + destruct (kind_check Delta ty1); [|discriminate].
        destruct k; [discriminate|discriminate].
Qed.


Theorem kind_checking_complete : forall (Delta : list (binderTyname * kind)) (ty : ty) (kind : kind),
    has_kind Delta ty kind -> kind_check Delta ty = Some kind.
Proof.
    intros Delta ty kind Hkind.
    induction Hkind; simpl.
    - (* Var *)
      apply H.
    - (* Ty_Fun *)
      rewrite -> IHHkind1.
      rewrite -> IHHkind2.
      reflexivity.
    - (* Ty_IFix *)
      rewrite -> IHHkind1.
      rewrite -> IHHkind2.
      rewrite -> eqb_kind_refl.
      reflexivity.
    - (* Ty_Forall *)
      rewrite -> IHHkind.
      reflexivity.
    - (* Ty_Builtin *)
      apply kind_checking_default_uni_complete in H.
      assumption.
    - (* Ty_Lam *)
      rewrite -> IHHkind.
      reflexivity.
    - (* Ty_App *) 
      rewrite -> IHHkind1. 
      rewrite -> IHHkind2. 
      rewrite -> eqb_kind_refl. 
      reflexivity.
Qed.