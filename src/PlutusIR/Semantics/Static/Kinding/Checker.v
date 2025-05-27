Require Import PlutusCert.PlutusIR.Analysis.Equality.
Require Import PlutusCert.PlutusIR.Semantics.Static.Kinding.Kinding.
Require Import PlutusCert.PlutusIR.

Require Import Coq.Bool.Bool.
Require Import PlutusCert.Util.List.
Require Import Coq.Lists.List.

From PlutusCert Require Import Util.



Fixpoint kind_check_default_uni (d : DefaultUni) : option kind :=
  match d with
  | DefaultUniInteger 
  | DefaultUniByteString 
  | DefaultUniString 
  | DefaultUniUnit 
  | DefaultUniBool 
  | DefaultUniData 
  | DefaultUniBLS12_381_G1_Element 
  | DefaultUniBLS12_381_G2_Element 
  | DefaultUniBLS12_381_MlResult => Some Kind_Base
  | DefaultUniApply t t' =>
      match (kind_check_default_uni t, kind_check_default_uni t') with
      | (Some (Kind_Arrow k k'), Some k'') => if Kind_eqb k'' k then Some k' else None
      | _ => None
      end
  | DefaultUniProtoPair => Some (Kind_Arrow Kind_Base (Kind_Arrow Kind_Base Kind_Base))
  | DefaultUniProtoList => Some (Kind_Arrow Kind_Base Kind_Base)
  end.

(* Tactic to simplify proofs containing hypotheses of the form
match x with
| A => Some alpha
| B _ _ => None
end = Some beta
to conclude x = A and Some alpha = Some beta.
*)
Ltac destruct_match :=
  match goal with
  | H : (match ?X with _ => _ end = _ ) |- _ => destruct X eqn:?; try discriminate
  end.

Lemma kind_checking_default_uni_sound : forall d k,
    kind_check_default_uni d = Some k -> |-*_uni d : k.
Proof with eauto.
  intros d k H. generalize dependent k.
  induction d; intros k H; inversion H; try constructor.
  - (* DefaultUniApply*) 
    repeat destruct_match.
    apply Kind_eqb_eq in Heqb.
    subst.
    apply K_DefaultUniApply with (k := k1_1).
    + apply IHd1.
      inversion H1.
      reflexivity.
    + apply IHd2.
      inversion H1.
      reflexivity. 
Defined.

Lemma kind_checking_default_uni_complete : forall d k,
    |-*_uni d : k -> kind_check_default_uni d = Some k.
Proof.
  intros d k H.
  induction H; simpl; try reflexivity.
  - (* DefaultUniApply *) 
    rewrite -> IHhas_kind_uni1.
    rewrite -> IHhas_kind_uni2.
    rewrite -> Kind_eqb_refl.
    reflexivity.
Qed.

Fixpoint kind_check (Delta : list (binderTyname * kind)) (ty : ty) : (option kind) :=
    match ty with
    | Ty_Var X => 
        lookup X Delta
    | Ty_Fun T1 T2 => 
        match (kind_check Delta T1, kind_check Delta T2) with
        | (Some Kind_Base, Some Kind_Base) => Some Kind_Base
        | (_, _) => None
        end
    | Ty_IFix F T => 
        match kind_check Delta T with
        | Some K => match kind_check Delta F with
            | Some (Kind_Arrow (Kind_Arrow K1 Kind_Base) (Kind_Arrow K2 Kind_Base)) =>
                if andb (Kind_eqb K K1) (Kind_eqb K K2) then Some Kind_Base else None
            | _ => None
            end
        | _ => None
        end
    | Ty_Forall X K T =>
        match kind_check ((X, K) :: Delta) T with
        | Some Kind_Base => Some Kind_Base
        | _ => None
        end
    | Ty_Builtin d =>
        match kind_check_default_uni d with
        | Some Kind_Base => Some Kind_Base
        | _ => None
        end
    | Ty_Lam X K1 T => 
        match kind_check ((X, K1) :: Delta) T with
        | Some K2 => Some (Kind_Arrow K1 K2)
        | _ => None
        end
    | Ty_App T1 T2 => 
        match (kind_check Delta T1, kind_check Delta T2) with
        | (Some (Kind_Arrow K11 K2), Some K12) =>
            if Kind_eqb K11 K12 then Some K2 else None
        | (_, _) => None
        end
    | Ty_SOP Tss => 
      if (forallb (fun Ts => 
              (forallb (fun T => match kind_check Delta T with 
                                      | Some Kind_Base => true
                                      | _ => false
                                end) Ts)) 
                Tss) then Some Kind_Base else None
    end.

Theorem kind_checking_sound : forall Delta ty kind,
    kind_check Delta ty = Some kind -> has_kind Delta ty kind.
Proof.
    intros Delta ty. generalize dependent Delta.
    induction ty using ty__ind; intros Delta kind Htc; inversion Htc.
    - (* Var *) 
      apply K_Var.
      assumption.
    - (* Ty_Fun *) 
      repeat destruct_match.
      inversion H0.
      subst kind.
      apply K_Fun; 
      [apply IHty1| apply IHty2]; 
      assumption.
    - (* Ty_IFix *) 
      repeat destruct_match.
      inversion H0.
      subst kind.
      remember (kind_check Delta ty2) as K.
      apply K_IFix with (K := k). 
      + apply IHty2.
        rewrite <- HeqK.
        assumption.
      + apply IHty1.
        apply andb_true_iff in Heqb.
        destruct Heqb as [eqb1 eqb2].
        apply Kind_eqb_eq in eqb1.
        apply Kind_eqb_eq in eqb2.
        subst...
        assumption.
    - (* Ty_Forall *)
      repeat destruct_match.
      inversion H0.
      
      apply K_Forall.
      apply IHty.
      assumption.
    - (* Ty_Builtin *)
      repeat destruct_match.
      inversion H0; subst.
      constructor.
      eapply kind_checking_default_uni_sound.
      assumption.
    - (* Ty_Lam *)
      destruct_match.
      inversion H0.
      apply K_Lam. 
      apply IHty.
      assumption.
    - (* Ty_App *) 
      remember (kind_check Delta ty2) as K1.
      destruct K1 as [k1|]; repeat destruct_match.
      apply K_App with (K1 := k1).  
        + apply IHty1.
          inversion H0.
          apply Kind_eqb_eq in Heqb.
          subst.
          assumption.
        + apply IHty2.
          rewrite HeqK1.
          reflexivity. 
    - destruct_match.
      inversion H1; subst.
      eapply K_SOP.
      clear H1.
      inversion H; subst; auto.
      constructor.
      + apply Forall_forall.
        intros.
        eapply Forall_forall with (x := x0) in H0; auto.
        eapply H0.
        inversion Heqb.
        apply andb_true_iff in H4 as [H4 _].
        eapply forallb_forall with (x := x0) in H4; auto.
        repeat destruct_match; subst; auto.
      + apply Forall_forall; intros.
        apply Forall_forall with (x := x0) in H1; auto.
        apply Forall_forall; intros.
        apply Forall_forall with (x := x1) in H1; auto.
        apply H1.


        inversion Htc.
        destruct_match; subst; auto.
        apply andb_true_iff in Heqb0 as [Heqb01 Heqb02].
        apply forallb_forall with (x :=x0) in Heqb02; auto.
        
        apply forallb_forall with (x := x1) in Heqb02; auto.
        repeat destruct_match; subst; auto.
Qed.


Section ty__ind_set.
  Unset Implicit Arguments.

  (* Variable for the property to prove about `ty` *)
  Variable (P : ty -> Set).

  (* Hypotheses for each constructor of `ty` *)
  Context
    (H_Var : forall (X : tyname), P (Ty_Var X))
    (H_Fun : forall (T1 T2 : ty), P T1 -> P T2 -> P (Ty_Fun T1 T2))
    (H_IFix : forall (F T : ty), P F -> P T -> P (Ty_IFix F T))
    (H_Forall : forall (X : binderTyname) (K : kind) (T : ty), P T -> P (Ty_Forall X K T))
    (H_Builtin : forall (T : DefaultUni), P (Ty_Builtin T))
    (H_Lam : forall (X : binderTyname) (K : kind) (T : ty), P T -> P (Ty_Lam X K T))
    (H_App : forall (T1 T2 : ty), P T1 -> P T2 -> P (Ty_App T1 T2))
    (H_SOP : forall (Tss : list (list ty)), ForallT (ForallT P) Tss -> P (Ty_SOP Tss)).

  (* Main induction principle for `ty` *)
  Fixpoint ty__ind_set (T : ty) : P T :=
    match T with
    | Ty_Var X => H_Var X
    | Ty_Fun T1 T2 => H_Fun T1 T2 (ty__ind_set T1) (ty__ind_set T2)
    | Ty_IFix F T => H_IFix F T (ty__ind_set F) (ty__ind_set T)
    | Ty_Forall X K T => H_Forall X K T (ty__ind_set T)
    | Ty_Builtin T => H_Builtin T
    | Ty_Lam X K T => H_Lam X K T (ty__ind_set T)
    | Ty_App T1 T2 => H_App T1 T2 (ty__ind_set T1) (ty__ind_set T2)
    | Ty_SOP Tss =>
        H_SOP Tss ((fix list_list_ind (tss : list (list ty)) : ForallT (ForallT P) tss :=
          match tss with
          | nil => ForallT_nil
          | ts :: tss' =>
              ForallT_cons
                ((fix list_ind (ts : list ty) : ForallT P ts :=
                   match ts with
                   | nil => ForallT_nil
                   | t :: ts' => 
                       ForallT_cons (ty__ind_set t) (list_ind ts')
                   end) ts)
                (list_list_ind tss')
          end) Tss)
    end.

End ty__ind_set.

(* Axiomatized so we can run typechecker on programs without TYSOP*)
Axiom kind_checking_sound_set_TySOP : forall x l Delta,
ForallT
  (ForallT
  (fun T : ty => Delta |-*s T : Kind_Base))
  (x :: l).

(* Identical to the above, but for Set*)
Theorem kind_checking_sound_set : forall Delta ty kind,
    kind_check Delta ty = Some kind -> has_kind_set Delta ty kind.
Proof.
    intros Delta ty. generalize dependent Delta.
    induction ty using ty__ind_set; intros Delta kind Htc; inversion Htc.
    - (* Var *) 
      apply K_Var_set.
      assumption.
    - (* Ty_Fun *) 
      repeat destruct_match.
      inversion H0.
      subst kind.
      apply K_Fun_set; 
      [apply IHty1| apply IHty2]; 
      assumption.
    - (* Ty_IFix *) 
      repeat destruct_match.
      inversion H0.
      subst kind.
      remember (kind_check Delta ty2) as K.
      apply K_IFix_set with (K := k). 
      + apply IHty2.
        rewrite <- HeqK.
        assumption.
      + apply IHty1.
        apply andb_true_iff in Heqb.
        destruct Heqb as [eqb1 eqb2].
        apply Kind_eqb_eq in eqb1.
        apply Kind_eqb_eq in eqb2.
        subst...
        assumption.
    - (* Ty_Forall *)
      repeat destruct_match.
      inversion H0.
      
      apply K_Forall_set.
      apply IHty.
      assumption.
    - (* Ty_Builtin *)
      repeat destruct_match; subst.
      inversion H0; subst.
      apply kind_checking_default_uni_sound in Heqo.
      apply K_Builtin_set.
      assumption.
    - (* Ty_Lam *)
      destruct_match.
      inversion H0.
      apply K_Lam_set. 
      apply IHty.
      assumption.
    - (* Ty_App *) 
      remember (kind_check Delta ty2) as K1.
      destruct K1 as [k1|]; repeat destruct_match.
      apply K_App_set with (K1 := k1).  
        + apply IHty1.
          inversion H0.
          apply Kind_eqb_eq in Heqb.
          subst.
          assumption.
        + apply IHty2.
          rewrite HeqK1.
          reflexivity. 
    - (* Ty_SOP *)
      destruct_match.
      inversion H1; subst.
      eapply K_SOP_set.
      clear H1.
      inversion H; subst; auto.
      constructor.
      apply kind_checking_sound_set_TySOP.
      (* ADMIT: Ty_SOP ForallT_Forall necessary? Prop vs Type *)
Qed.
  

Lemma kind_checking_complete_TYSOP Tss Δ : 
        Forall
          (Forall
          (fun T : ty => kind_check Δ T = Some Kind_Base))
          Tss -> (if
        forallb (fun Ts : list ty =>
        forallb (fun T : ty => match kind_check Δ T with
        | Some Kind_Base => true
        | _ => false
        end) Ts)
          Tss then Some Kind_Base
        else None) =
        Some Kind_Base.
Proof.
  intros.
  induction Tss; simpl; auto.
  induction a; simpl; auto.
  - apply IHTss. inversion H; auto.
  - inversion H; subst; auto.
    inversion H2; subst; auto.
    rewrite H4.
    simpl.
    assert (forallb (fun T : ty =>
        match kind_check Δ T with
        | Some Kind_Base => true
        | _ => false
        end)
          a0 = true).
    {  clear H H2 H3 H4 IHa IHTss.
      induction a0; simpl; auto. 
      inversion H5; subst; auto. rewrite H1. simpl.
      auto. }
    rewrite H0. simpl.
    apply IHTss. auto.
Qed.

Theorem kind_checking_complete : forall (Delta : list (binderTyname * kind)) (ty : ty) (kind : kind),
    has_kind Delta ty kind -> kind_check Delta ty = Some kind.
Proof.
    intros Delta ty kind Hkind.
    induction Hkind using Kinding.has_kind__ind; simpl.
    - (* Var *)
      apply H.
    - (* Ty_Fun *)
      rewrite -> IHHkind.
      rewrite -> IHHkind0.
      reflexivity.
    - (* Ty_IFix *)
      rewrite -> IHHkind.
      rewrite -> IHHkind0.
      rewrite -> Kind_eqb_refl.
      reflexivity.
    - (* Ty_Forall *)
      rewrite IHHkind.
      auto.
    - (* Ty_Builtin *)
      
      apply kind_checking_default_uni_complete in H.
      rewrite H.
      reflexivity.
    - (* Ty_Lam *)
      rewrite IHHkind.
      auto.
    - (* Ty_App *) 
      rewrite -> IHHkind. 
      rewrite -> IHHkind0. 
      rewrite -> Kind_eqb_refl. 
      reflexivity.
    - (* Ty_SOP *)
      apply kind_checking_complete_TYSOP; auto.
Defined.

Theorem prop_to_type : forall Δ T K, has_kind Δ T K -> has_kind_set Δ T K.
Proof.
    intros Δ T K Hhk.
    apply kind_checking_complete in Hhk. (* we cannot destruct on kind_check Δ T, because then we get some arbirtary kind*)
    apply kind_checking_sound_set in Hhk.
    auto.
Qed.
