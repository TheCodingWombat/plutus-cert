
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From PlutusCert Require Import 
    Normalisation.Normalisation 
    Norm_sound_complete
    PlutusIR 
    Static.Typing
    Util.List
    Static.Util
    Equality
    Kinding.Checker
    Util
    SubstituteTCA
    UniqueTypes
    Binders_Wellkinded
    BaseKindedness.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.

Scheme has_type_mut_ind := Induction for has_type Sort Prop
with bs_wf_mut_ind := Induction for bindings_well_formed_rec Sort Prop
with bs_wf_nonrec_mut_ind := Induction for bindings_well_formed_nonrec Sort Prop
with b_wf_mut_ind := Induction for binding_well_formed Sort Prop.

Fixpoint allbmap {A : Type} (f : A -> bool) (bs : list A) : bool :=
    match bs with
    | [] => true
    | b::bs => andb (f b) (allbmap f bs)
    end.

Lemma allb_element_true : forall A f bs b, In b bs -> @allbmap A f bs = true -> f b = true.
Proof.
  intros.
  induction bs.
  - inversion H.
  - simpl in H0.
    destruct H.
    + subst.
      simpl in H0.
      apply andb_true_iff in H0.
      destruct H0.
      assumption.
    + apply andb_true_iff in H0.
      destruct H0.
      apply IHbs; auto.
Qed.

Lemma allbmap_each : forall A f bs, (forall b, In b bs -> f b = true) -> @allbmap A f bs = true.
Proof.
  intros.
  induction bs.
  - simpl. reflexivity.
  - simpl.
    apply andb_true_iff.
    split.
    + apply H. left. reflexivity.
    + apply IHbs.
      intros.
      apply H.
      right. assumption.
Qed.

(* Find instead of in_dec for performance?*)
Fixpoint no_dup_fun (xs : list string) := 
  match xs with
  | nil => true
  | (x::xs) => if in_dec string_dec x xs then false else no_dup_fun xs
  end.

Lemma no_dup_fun_sound : forall xs, no_dup_fun xs = true -> NoDup xs.
Proof.
Admitted.

Lemma no_dup_fun_complete : forall xs, NoDup xs -> no_dup_fun xs = true.
Proof.
Admitted.

Definition is_KindBase (k : option kind) : bool :=
  match k with 
  | Some Kind_Base => true
  | _ => false
  end.

Definition constructor_well_formed_check (Δ : list (binderTyname * kind)) (v : vdecl) (Tr : ty ) : bool :=
  match v with
  | VarDecl x T => let (targs, tr') := splitTy T in
          Ty_eqb Tr tr' && allbmap (fun U => is_KindBase (kind_check Δ U)) targs
  end.

(* Idea Jacco: pass the recursively called type_check function as an argument even though it is not defined yet 
Make another version that already has type_check as argument after type_check is defined.
*)
Definition binding_well_formed_check 
  (type_check' : ((list (binderTyname * kind)) -> (list (binderName * ty)) -> term -> option ty)) 
  (Δ : list (binderTyname * kind)) (Γ : list (binderName * ty)) (rec : recursivity) binding : bool :=
    match binding with
    | (TypeBind (TyVarDecl X K) T) => match kind_check Δ T with
                                      | Some K' => Kind_eqb K K' (* is this K the same as in the pattern match to the left? it should be*)
                                      | _ => false
                                      end
    | (TermBind s (VarDecl x T) t) => match kind_check Δ T with
                                      | Some Kind_Base => 
                                        match type_check' Δ Γ t with   
                                        | Some Tn => match normaliser_Jacco Δ T with
                                                    | Some Tn' => Ty_eqb Tn Tn'
                                                    | _ => false
                                                    end
                                        | _ => false
                                        end
                                      | _ => false
                                      end
    | (DatatypeBind (Datatype XK YKs matchFunc cs)) => 
      let dtd := Datatype XK YKs matchFunc cs in
      let X := tvdecl_name XK in
      let Ys := map tvdecl_name YKs in
      if no_dup_fun (X :: Ys) && no_dup_fun (map vdecl_name cs) then
        let Δ_ns := match rec with
                    | NonRec => drop_Δ' Δ [X]
                    | Rec => Δ
                    end in
        let Δ' := rev (map fromDecl YKs) ++ Δ_ns in
        let Tres := constrLastTyExpected dtd in
        if allbmap (fun c => constructor_well_formed_check Δ' c Tres) cs then
          match rec with
            | NonRec => match kind_check (fromDecl XK :: Δ') Tres with
                        | Some Kind_Base => true 
                        | _ => false
                        end
            | Rec =>    match kind_check Δ' Tres with
                        | Some Kind_Base => true 
                        | _ => false  
                        end
          end
        else false
      else false
    end.

(* first argument represents binding_well_formed with the type_check already passed in *)
Definition bindings_well_formed_nonrec_check : 
  ((list (binderTyname * kind)) -> (list (binderName * ty)) -> recursivity -> binding -> bool) ->
  list (binderTyname * kind) -> (list (binderName * ty)) -> (list binding) -> bool :=
  fun b_wf =>
  fix f Δ Γ bs :=
    match bs with
      | (b::bs') =>
            match (map_normaliser (insert_deltas_rec (binds_Gamma b) (binds_Delta b ++ Δ))) with
            | Some bsGn =>
              b_wf Δ Γ NonRec b && f ((binds_Delta b) ++ Δ) (bsGn ++ Γ) bs'
            | _ => false
            end
      | _ => true
    end.

Definition bindings_well_formed_rec_check : (binding -> bool) -> list binding -> bool :=
  fun b_wf =>
  fix f bs :=
    match bs with
      | (b::bs') => b_wf b && f bs'
      | _ => true
    end.

Fixpoint type_check (Δ : list (binderTyname * kind)) (Γ : list (binderName * ty)) (term : term) {struct term} : (option ty) :=
    match term with
    | Var x => lookup x Γ >>= fun T => 
                match kind_check Δ T with
                | Some Kind_Base => normaliser_Jacco Δ T
                | _ => None
                end
    | LamAbs x T1 t => 
        normaliser_Jacco Δ T1 >>= fun T1n =>
        match type_check Δ ((x, T1n) :: Γ) t, kind_check Δ T1 with
        | Some T2, Some Kind_Base => Some (Ty_Fun T1n T2) (* TODO: no normalisation of T2? Is it always normal? In the has_type efinition it is called T2n, so maybe it is*)
        | _, _ => None
        end
    | Apply t1 t2 => (* TODO: normalisation? *)
        match type_check Δ Γ t1, type_check Δ Γ t2 with
        | Some (Ty_Fun T1 T2), Some T1' =>
            if Ty_eqb T1 T1' then Some T2 else None
        | _, _ => None
        end
    | TyAbs X K t => (* TODO: normalisation T?*)
      (* If K in Δ, then 
          1. create fresh K'
          2 rename K to K' in t 
           
           final type    Ty_Forall X K' T
          *)

        match type_check ((X, K) :: Δ) (drop_ty_var X Γ) t with
        | Some T => Some (Ty_Forall X K T)
        | _ => None
        end
    | TyInst t1 T2 => (* TODO: normalisation T1?*)
        match type_check Δ Γ t1, kind_check Δ T2 with (* TODO: first we check that it kind and type checks here, and then normaliser_Jacco does it again. Feels a little off*)
        | Some (Ty_Forall X K2 T1), Some K2' =>
            (* match kind_check ((X, K2)::Δ) T1 with
            | Some Kind_Base => *)
            if Kind_eqb K2 K2' then 
                normaliser_Jacco Δ T2 >>= fun T2n =>
                normaliser_Jacco Δ (substituteTCA X T2n T1) >>= fun T0n =>
                Some T0n
            else None
            (* | _ => None
            end *)
        | _, _ => None
        end
    | IWrap F T M =>
        match kind_check Δ T, kind_check Δ F, type_check Δ Γ M with
        | Some K, Some (Kind_Arrow (Kind_Arrow K' Kind_Base) (Kind_Arrow K'' Kind_Base)), Some T0n
            => if andb (Kind_eqb K K') (Kind_eqb K K'') then
                    normaliser_Jacco Δ T >>= fun Tn =>
                    normaliser_Jacco Δ F >>= fun Fn =>
                    normaliser_Jacco Δ (unwrapIFix Fn K Tn) >>= fun T0n' =>
                    if Ty_eqb T0n T0n' then 
                        Some (Ty_IFix Fn Tn)
                    else None 
                else None 
        | _, _, _ => None
        end
    | Unwrap M =>
        match type_check Δ Γ M with
            | Some (Ty_IFix F T) =>
                match kind_check Δ T with
                    | Some K =>
                          normaliser_Jacco Δ (unwrapIFix F K T) >>= fun T0n => Some T0n
                        
                    | _  => None
                    end 
            | _ => None
            end
    | Constant (ValueOf T a) => Some (Ty_Builtin T)
    | Builtin f =>
        let T := lookupBuiltinTy f in
        normaliser_Jacco Δ T >>= fun Tn =>
        Some Tn
    | Error S' => normaliser_Jacco Δ S' >>= fun S'n => match kind_check Δ S' with
        | Some Kind_Base => Some S'n
        | _ => None
        end
    | Let NonRec bs t =>
        let Δ' := flatten (map binds_Delta bs) ++ Δ in
        let xs := (insert_deltas_bind_Gamma_nr bs Δ) in
          map_normaliser xs >>= fun bsgn => (* TODO:  Δ' ?*) (* TODO different Δ*)
          let Γ' := bsgn ++ Γ in
          if (bindings_well_formed_nonrec_check (binding_well_formed_check type_check) Δ Γ bs) then 
            type_check Δ' Γ' t >>= fun T =>
              let Δ_no_esc := drop_Δ Δ bs in
              match kind_check Δ_no_esc T with
              | Some Kind_Base => Some T
              | _ => None
              end
          else None
    | Let Rec bs t => 
        if no_dup_fun (btvbs bs) && no_dup_fun (bvbs bs) then
          let Δ' := flatten (map binds_Delta bs) ++ Δ in
          let xs := (insert_deltas_rec (flatten (map binds_Gamma bs)) Δ') in
            map_normaliser xs >>= fun bsgn =>
            let Γ' := bsgn ++ Γ in
              if (bindings_well_formed_rec_check (binding_well_formed_check type_check Δ' Γ' Rec) bs) then 
                type_check Δ' Γ' t >>= fun T =>
                  let Δ_no_esc := drop_Δ Δ bs in
                  match kind_check Δ_no_esc T with
                  | Some Kind_Base => Some T
                  | _ => None
                    end 
              else None
          else None
    | _ => None (* TODO: Case and Constr?? *)
    end.

Section term_recursivity_rect.
  Variable (P : term -> Type).
  Variable (Q : binding -> Type).
  Variable (R : list binding -> Type).
  Variable (S : list binding -> Type).

  Context
    (* (H_Let     : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t)) *)
    (H_LetRec     : forall bs t, R bs -> P t -> P (Let Rec bs t))
    (H_LetNonRec  : forall bs t, S bs -> P t -> P (Let NonRec bs t))
    (H_Var     : forall s, P (Var s))
    (H_TyAbs   : forall s (k : kind) (t : term), P t -> P (TyAbs s k t))
    (H_LamAbs  : forall s t (t0 : term), P t0 -> P (LamAbs s t t0))
    (H_Apply   : forall t : term, P t -> forall t0 : term, P t0 -> P (Apply t t0))
    (H_Constant : forall (c : constant), P (Constant c))
    (H_Builtin : forall d : DefaultFun, P (Builtin d))
    (H_TyInst  : forall t : term, P t -> forall t0 : ty, P (TyInst t t0))
    (H_Error   : forall t : ty, P (Error t))
    (H_IWrap   : forall (t t0 : ty) (t1 : term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap  : forall t : term, P t -> P (Unwrap t))
    (H_Constr  : forall (i : nat) T (ts : list (term)), ForallT P ts -> P (Constr T i ts))
    (H_Case   : forall T t, P t -> forall ts, ForallT P ts -> P (Case T t ts)).

  Context
    (H_TermBind    : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind    : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Context
    (H_cons        : forall b bs, Q b -> R bs -> R (b :: bs))
    (H_nil         : R nil).

  Context
    (H_consS      : forall b bs, Q b -> S bs -> S (b :: bs))
    (H_nilS       : S nil).

  Definition bindings_rect'' (binding_rect'' : forall (b : binding), Q b) :=
    fix bindings_rect'' bs :=
    match bs return R bs with
      | nil       => @H_nil
      | cons b bs => @H_cons _ bs (binding_rect'' b) (bindings_rect'' bs)
    end.

  Definition bindings_nonrect'' (binding_rect'' : forall (b : binding), Q b) :=
    fix bindings_nonrect'' bs :=
    match bs return S bs with
      | nil       => @H_nilS
      | cons b bs => @H_consS _ bs (binding_rect'' b) (bindings_nonrect'' bs)
    end.

  Definition terms_rect'' (term_rect : forall (t : term), P t) :=
    fix terms_rect' ts :=
    match ts as p return ForallT P p with
      | nil       => ForallT_nil
      | cons t ts => ForallT_cons (term_rect t) (terms_rect' ts)
    end.

  Fixpoint term_rect'' (t : term) : P t :=
    match t with
      | Let Rec bs t    => @H_LetRec bs t (bindings_rect'' binding_rect'' bs) (term_rect'' t)
      | Let NonRec bs t => @H_LetNonRec bs t (bindings_nonrect'' binding_rect'' bs) (term_rect'' t)
      | Var n           => @H_Var n
      | TyAbs n k t     => @H_TyAbs n k t (term_rect'' t)
      | LamAbs n ty t   => @H_LamAbs n ty t (term_rect'' t)
      | Apply s t       => @H_Apply s (term_rect'' s) t (term_rect'' t)
      | TyInst t ty     => @H_TyInst t (term_rect'' t) ty
      | IWrap ty1 ty2 t => @H_IWrap ty1 ty2 t (term_rect'' t)
      | Unwrap t        => @H_Unwrap t (term_rect'' t)
      | Error ty        => @H_Error ty
      | Constant c      => @H_Constant c
      | Builtin f       => @H_Builtin f
      | Constr i T ts     => @H_Constr T i ts (terms_rect'' term_rect'' ts)
      | Case T t ts      => @H_Case T t (term_rect'' t) ts (terms_rect'' term_rect'' ts)
    end
  with binding_rect'' (b : binding) : Q b :=
    match b with
      | TermBind s v t   => @H_TermBind s v t (term_rect'' t)
      | TypeBind v ty    => @H_TypeBind v ty
      | DatatypeBind dtd => @H_DatatypeBind dtd
    end.
End term_recursivity_rect.

Require Import Coq.Strings.String.
Open Scope string_scope.

Definition my_Gamma : list (string * ty) := (("x", Ty_App (Ty_Lam "y" Kind_Base (Ty_Var "y")) (Ty_Builtin DefaultUniInteger))::nil). 

  
  

Lemma constructor_well_formed_sound : 
  forall Δ c T, constructor_well_formed_check Δ c T = true -> Δ |-ok_c c : T.
Proof. 
  intros.
  destruct c.
  inversion H.
  remember (splitTy t).
  destruct p as [targs tr'].
  apply andb_true_iff in H1.
  destruct H1.
  apply Ty_eqb_eq in H0.
  subst.
  eapply W_Con; eauto.
  simpl in H1.
  intros.
  apply (allb_element_true ty _ _ _ H0) in H1.
  unfold is_KindBase in H1.
  repeat destruct_match.
  subst.
  now apply kind_checking_sound in Heqo.
Qed.

Lemma constructor_well_formed_complete : 
  forall Δ c T, Δ |-ok_c c : T -> constructor_well_formed_check Δ c T = true.
Proof.
  intros.
  destruct c.
  inversion H.
  subst.
  simpl.
  destruct (splitTy t) as [targs' T'].
  inversion H2.
  subst.
  apply andb_true_iff.
  split.
  - apply Ty_eqb_refl.
  - apply allbmap_each.
    intros.
    unfold is_KindBase.
    specialize (H4 b0 H0).
    apply kind_checking_complete in H4.
    rewrite H4.
    reflexivity.
Qed.

Lemma insert_remove_deltas_id xs Δ :
  xs = remove_deltas (insert_deltas_rec xs Δ).
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    destruct a as [x T].
    unfold remove_deltas. fold (@remove_deltas string).
    f_equal.
    assumption.
Qed.

Lemma insert_remove_deltas_nr_id xs Δ :
  flatten (map binds_Gamma xs) = remove_deltas (insert_deltas_bind_Gamma_nr xs Δ).
Proof.
  generalize dependent Δ.
  induction xs; intros.
  - reflexivity.
  - simpl.
    rewrite flatten_cons.
    rewrite remove_deltas_app.

    rewrite <- insert_remove_deltas_id.
    f_equal; auto.
Qed.

From Coq Require Import Program.Equality.

Theorem type_checking_sound : 
 forall Δ Γ t ty, type_check Δ Γ t = Some ty -> (Δ ,, Γ |-+ t : ty).
Proof with (try apply kind_checking_sound; try eapply normaliser_Jacco_sound; eauto).
  intros Δ Γ t ty.
  revert Δ Γ ty.
  eapply term_rect'' with 
    (P := fun t => forall Δ Γ ty, type_check Δ Γ t = Some ty -> Δ,, Γ |-+ t : ty)
    (Q := fun b => forall Δ Γ rec, binding_well_formed_check type_check Δ Γ rec b = true -> binding_well_formed Δ Γ rec b)
    (R := fun bs => forall Δ Γ, bindings_well_formed_rec_check (binding_well_formed_check type_check Δ Γ Rec) bs = true -> bindings_well_formed_rec Δ Γ bs)
    (S := fun bs => forall Δ Γ, bindings_well_formed_nonrec_check (binding_well_formed_check type_check) Δ Γ bs = true -> bindings_well_formed_nonrec Δ Γ bs).
    repeat destruct_match.
  - (* Case: Let Rec*)
    intros bs t0.
    intros P.
    intros Ptype Δ Γ T Htc.
    inversion Htc.
    unfold bind in H0.
    repeat destruct_match.
    inversion H0; subst.
    apply andb_true_iff in Heqb. destruct Heqb.
    eapply T_LetRec; auto.
    + apply no_dup_fun_sound. auto.
    + apply no_dup_fun_sound. auto.
    + eapply map_normaliser_sound in Heqo.
      rewrite <- insert_remove_deltas_id in Heqo.
      eauto.
    + apply (map_normaliser_sound) in Heqo; eauto.
    + eapply Ptype; eauto.
    + now apply kind_checking_sound in Heqo1.
  - (* Case Let NONRec *)
    intros bs t0.
    intros P.
    intros Q.
    intros.
      inversion H.
      unfold bind in H1.
      destruct_match.
      repeat destruct_match.
      inversion H1; subst.
      eapply T_Let with (Δ' := (flatten (map binds_Delta bs) ++ Δ)%list); auto.      
      * apply (map_normaliser_sound) in Heqo. 
        rewrite <- insert_remove_deltas_nr_id in Heqo.
        exact Heqo.
      * eapply Q. auto.
      * apply kind_checking_sound in Heqo1.  auto.
  - intros. 
    inversion H; subst.
    unfold bind in H1.
    repeat destruct_match; subst.
    remember H1 as H1_copy; clear HeqH1_copy.
    apply T_Var with (T := t0); auto.
    eapply kind_checking_sound in Heqo0; auto.
    now apply normaliser_Jacco_sound in H1_copy.
  - intros. 
    inversion H0.
    unfold bind in H0.
    repeat destruct_match.
    inversion H2.
    subst.
    eapply T_TyAbs...
  - intros.
    inversion H0.
    unfold bind in H2.
    repeat destruct_match.
    inversion H2.
    subst.
    apply T_LamAbs...
  - intros.
    inversion H1.
    repeat destruct_match.
    inversion H3; subst.
    eapply T_Apply with (T1n := t3_1).
    + eapply H; eauto.
    + eapply H0; eauto.
      apply Ty_eqb_eq in Heqb.
      now subst.
  - intros.
    inversion H.
    unfold bind in H1.
    repeat destruct_match.
    inversion H1; subst.
    apply T_Constant.
  - intros.
    inversion H.
    unfold bind in H1.
    repeat destruct_match.
    inversion H1; subst.
    apply normaliser_Jacco_sound in Heqo.
    now apply T_Builtin with (T := lookupBuiltinTy d).
  - intros. inversion H0. unfold bind in H2. repeat destruct_match.
    inversion H2. subst.
    apply Kind_eqb_eq in Heqb0.
    subst.
    apply T_TyInst with (X := b) (K2 := k0) (T1n := t3) (T2n := t4); eauto.
    + apply kind_checking_sound. auto.
    + apply normaliser_Jacco_sound in Heqo1. auto.
    + apply normaliser_Jacco_sound in Heqo2. auto.
  - intros.
    unfold type_check in H.
    
    
    unfold bind in H.
    repeat destruct_match.
    inversion H.
    subst.
    apply T_Error.
    + now apply kind_checking_sound.
    + apply normaliser_Jacco_sound in Heqo. 
      assumption.
  - intros.
    inversion H0.
    unfold bind in H2.
    repeat destruct_match.
    inversion H2.
    subst.
    apply Ty_eqb_eq in Heqb0.
    rewrite andb_true_iff in Heqb.
    destruct Heqb as [Heqb1 Heqb2].
    apply Kind_eqb_eq in Heqb1.
    apply Kind_eqb_eq in Heqb2.
    subst.
    apply T_IWrap with (K := k1_5) (T0n := t6)...
  - intros.
    inversion H0.
    unfold bind in H2.
    repeat destruct_match.
    inversion H2. subst.
    apply T_Unwrap with (Fn := t2_1) (Tn := t2_2) (K := k)...
  - intros.
    inversion H.
  - intros.
    inversion H0.
  - intros.
    inversion H0.
    repeat destruct_match.
    subst.
    apply W_Term with (Tn := t3).
    + apply kind_checking_sound in Heqo.
      assumption.
    + now apply normaliser_Jacco_sound in Heqo1.
    + apply Ty_eqb_eq in H2.
      subst.
      eapply H; eauto.
  - intros.
    inversion H.
    repeat destruct_match.
    apply W_Type.
    apply kind_checking_sound in Heqo.
    apply Kind_eqb_eq in H1.
    subst.
    assumption.
  - (* W_Data *)
    intros.
    inversion H.
    repeat destruct_match; subst.
    + (* NonRec *)
      apply andb_true_iff in Heqb0 as [Hdup1 Hdup2].
      
      repeat destruct_match; subst.
      eapply W_Data.
      * eauto.
      * reflexivity.
      * reflexivity.
      * constructor.
        -- auto.
        -- apply no_dup_fun_sound; auto.
      * apply no_dup_fun_sound. auto.
      * reflexivity.
      * reflexivity.
      * eauto.
      * intros.
        simpl.
        eauto.
        assert (constructor_well_formed_check (rev (map fromDecl l) ++ (drop_Δ' Δ [tvdecl_name t0])) c (Ty_Apps (Ty_Var (tvdecl_name t0)) (map Ty_Var (map tvdecl_name l))) = true).
        { 
            eapply (allb_element_true) in Heqb1.
          - exact Heqb1.
          - assumption.
        }
        apply constructor_well_formed_sound.
        auto.
      * eapply kind_checking_sound; eauto.
    + apply andb_true_iff in Heqb0 as [Hdup1 Hdup2].
      repeat destruct_match; subst.
      eapply W_Data; eauto.
      * constructor; auto.
        apply no_dup_fun_sound; auto.
      * apply no_dup_fun_sound; auto.
      * intros.
        simpl.
        assert (constructor_well_formed_check (rev (map fromDecl l) ++ Δ) c (Ty_Apps (Ty_Var (tvdecl_name t0)) (map Ty_Var (map tvdecl_name l))) = true).
        { eapply (allb_element_true) in Heqb1.
          - exact Heqb1.
          - assumption.
        }
        now apply constructor_well_formed_sound.
      * eapply kind_checking_sound; eauto.
  - intros.
    apply W_ConsB_Rec.
    + apply H.
      inversion H1.
      apply andb_true_iff in H3.
      destruct H3.
      rewrite H2.
      rewrite H3.
      auto.
    + eapply H0.
      inversion H1.
      apply andb_true_iff in H3.
      destruct H3.
      rewrite H2.
      rewrite H3.
      auto.
  - intros.
    apply W_NilB_Rec.
  - intros.
    inversion H1.
    destruct_match.
    apply andb_true_iff in H3.
    destruct H3.
    eapply W_ConsB_NonRec.
    + apply H.
      assumption.
    + apply map_normaliser_sound in Heqo.
      eauto.
      rewrite <- insert_remove_deltas_id in Heqo.
      exact Heqo.
    + eapply H0.
      intuition.
  - intros.
    apply W_NilB_NonRec.
Qed.

(* Hmmm, why does this rewrite?? This helper lemma is of course temporary TODO *)
Lemma test (T2n T1n : ty) Δ Γ t x :
    type_check Δ ((x, T1n)::Γ) t = Some T2n -> match type_check Δ ((x, T1n)::Γ) t with 
                    | Some T2 => Some (Ty_Fun T1n T2) 
                    | None => None
                end = Some (Ty_Fun T1n T2n). 
Proof.
    intros. now rewrite H.
Qed.

(* this doesnt work inline...*)
Lemma oof2 X K Δ Γ t Tn :
  type_check ((X, K) :: Δ) Γ t = Some Tn ->
  match type_check ((X, K) :: Δ) Γ t with
  | Some T => Some (Ty_Forall X K T)
  | None => None
  end = Some (Ty_Forall X K Tn).
Proof.
    intros.
    rewrite H.
    reflexivity.
Qed.

Lemma bool_if {A} (b : bool) (x y : A) :
  b = true -> (if b then x else y) = x.
Proof. intros ->; reflexivity. Qed.



Theorem type_checking_complete : forall Δ Γ t ty,
    (Δ ,, Γ |-+ t : ty) -> type_check Δ Γ t = Some ty.
Proof.
  intros.
  apply has_type_mut_ind with         
        (P := fun Δ Γ t T _ => type_check Δ Γ t = Some T)
        (P0 := fun Δ Γ l _ => bindings_well_formed_rec_check (binding_well_formed_check type_check Δ Γ Rec) l = true) 
        (P1 := fun Δ Γ l _ => bindings_well_formed_nonrec_check (binding_well_formed_check type_check) Δ Γ l = true )
        (P2 := fun Δ Γ rec b  _ => binding_well_formed_check type_check Δ Γ rec b = true) 
        ; simpl; auto; intros.
  - (*Case T_Var *)
    rewrite e. simpl. 
    eapply kind_checking_complete in h.
    rewrite h.
    eapply normaliser_Jacco_complete; eauto.
    eapply kind_checking_sound; eauto.
  - (* Case: T_LamAbs *)
    eapply (normaliser_Jacco_complete h) in n.
    rewrite n. simpl.
    apply kind_checking_complete in h; rewrite h.
    now apply test.
  - (* Case: T_Apply *)
    rewrite H0.
    rewrite H1.
    now rewrite -> Ty_eqb_refl.
  - (* Case: T_TyAbs *) 
    apply oof2; auto.
  - (* Case: T_Inst *)
    admit.
    (* rewrite H0.
    apply (normaliser_Jacco_complete h0) in n; rewrite n; simpl.
    apply kind_checking_complete in h0; rewrite h0.
    rewrite -> Kind_eqb_refl.
    
    assert (Δ0 |-* (substituteTCA X T2n T1n) : Kind_Base) as Hwk_subst.
    {
      assert (((X, K2)::Δ0) |-* T1n : Kind_Base).
      {
        apply has_type__basekinded in h.
        inversion h; subst.
        assumption.
      }
      eapply substituteTCA_preserves_kinding; eauto.
      eapply normaliser_preserves_kinding; eauto.
      eapply kind_checking_sound; eauto.
    }
    unfold bind.
    now apply (normaliser_Jacco_complete Hwk_subst) in n0; rewrite n0; simpl. *)
  - (* Case T_IWrap *)
    apply (normaliser_Jacco_complete h) in n; rewrite n; simpl.
    apply (normaliser_Jacco_complete h0) in n0; rewrite n0; simpl.

    assert (Δ0 |-* (unwrapIFix Fn K Tn) : Kind_Base).
    {
      eapply unwrapIFix__well_kinded; eauto.
      - eapply normaliser_preserves_kinding; eauto.
      - eapply normaliser_preserves_kinding; eauto.
    }

    apply kind_checking_complete in h; rewrite h.
    apply kind_checking_complete in h0; rewrite h0.
    (* apply kind_checking_complete in H1. *)
    apply (normaliser_Jacco_complete H1) in n1; rewrite n1; simpl.

    rewrite H0.
    rewrite Kind_eqb_refl; simpl.
    now rewrite Ty_eqb_refl.
  - (* Case: T_Unwrap*)
    rewrite H0.

    assert (Δ0 |-* (unwrapIFix Fn K Tn) : Kind_Base).
    {
      eapply unwrapIFix__well_kinded; eauto.
      apply has_type__basekinded in h.
      inversion h; subst.
      apply (unique_kinds Δ0 Tn K0 K H4) in h0; subst.
      assumption.
    }

    apply kind_checking_complete in h0; rewrite h0.
    unfold bind.
    apply (normaliser_Jacco_complete H1) in n; rewrite n.
    reflexivity.
  - (* Case: T_Builtin*)
    subst.
    eapply normaliser_Jacco_complete in n.
    rewrite n. simpl. reflexivity.
    apply lookupBuiltinTy__well_kinded. (* TODO: Is this true?*)
  - (* Case: T_Error *)
    unfold bind.
    apply (normaliser_Jacco_complete h) in n; rewrite n.
    apply kind_checking_complete in h; rewrite h.
    reflexivity.
  - (* Case: T_Let (NonRec)*)
    intros. simpl. subst.
    unfold bind.

    apply bs_nr_wf__map_wk in b.
    assert (map_normaliser (insert_deltas_bind_Gamma_nr bs Δ0) = Some bsGn).
    {
      assert (flatten (map binds_Gamma bs) = remove_deltas (insert_deltas_bind_Gamma_nr bs Δ0)).
      { 
        apply insert_remove_deltas_nr_id.
      }
      rewrite H2 in m.
      apply (map_normaliser_complete b) in m.
      assumption.
    }
    unfold bind.
    rewrite H2.
    rewrite H0.
    rewrite H1.
    
    apply kind_checking_complete in h0; rewrite h0; auto.
  - (* Case: T_LetRec *)
    destruct (no_dup_fun (btvbs bs) &&
no_dup_fun (bvbs bs)) eqn:no_dup_eqn.
    {
      intros. simpl. subst.
      apply bs_r_wf__map_wk in b.
      - assert ( (* insert then remove deltas is id*)
        (flatten (map binds_Gamma bs)) = remove_deltas (insert_deltas_rec (flatten (map binds_Gamma bs)) (flatten (map binds_Delta bs) ++
    Δ0))).
        {
          apply insert_remove_deltas_id.
        }
        rewrite H2 in m.
        apply (map_normaliser_complete b) in m.
        unfold bind.
        rewrite m.
        rewrite H0.
        rewrite H1.
        
        apply kind_checking_complete in h0; rewrite h0; reflexivity.
    }
    apply andb_false_iff in no_dup_eqn. exfalso.
    
    destruct no_dup_eqn.
    + apply no_dup_fun_complete in n. rewrite n in H2. discriminate H2.
    + apply no_dup_fun_complete in n0. rewrite n0 in H2. discriminate H2.
  - (* Case: ? *)
    intros. simpl. rewrite H0. auto.
  - (* Case: ? *)

    
    assert (binds_Gamma b = remove_deltas (insert_deltas_rec (binds_Gamma b) (binds_Delta b ++ Δ0))).
    {
      apply insert_remove_deltas_id.
    }
    rewrite H2 in m.
    apply (map_normaliser_complete) in m.
    + unfold bind.
      rewrite m.
      apply andb_true_iff.
      split.
      * auto.
      * eapply H1.
    + apply b_nr_wf__map_wk in b0; auto.

  - intros. simpl. rewrite H0.
    apply (normaliser_Jacco_complete h) in n; rewrite n.
    rewrite Ty_eqb_refl.
    apply kind_checking_complete in h; rewrite h.
    auto.
  - intros. simpl. apply kind_checking_complete in h; rewrite h. auto. apply Kind_eqb_eq. reflexivity.
  - (* W_Data *)
    destruct dtd.
    destruct rec.
    {
      inversion e; subst.
      destruct (in_dec string_dec (tvdecl_name XK) (map tvdecl_name YKs)) as [i | ni] eqn:Hindec.
      {
        exfalso.
        inversion n; subst.
        contradiction.
      }


      simpl.
      destruct (no_dup_fun (map tvdecl_name YKs) &&
        no_dup_fun (map vdecl_name cs)) eqn:no_dup.
    + inversion e; subst.
      apply no_dup_fun_complete in n.
      simpl in n.
      destruct_match.
      subst.
      clear e. clear n. clear n0. clear no_dup.
      induction cs; intros.
      -- simpl. 
         apply kind_checking_complete in y.
         simpl in y.
         rewrite y. reflexivity.
      -- assert (allbmap
          (fun c0 : vdecl =>
        constructor_well_formed_check
          (rev (map fromDecl YKs) ++ drop_Δ' Δ0 [tvdecl_name XK]) c0
          (Ty_Apps (Ty_Var (tvdecl_name XK)) (map Ty_Var (map tvdecl_name YKs))))
          (a :: cs) = true).
          {
            eapply andb_true_intro. split.
            eapply constructor_well_formed_complete.
            eapply c. apply in_eq.
            assert ((if
                      allbmap (fun c0 : vdecl =>
                      constructor_well_formed_check (rev (map fromDecl YKs) ++ drop_Δ' Δ0 [tvdecl_name XK]) c0 (Ty_Apps (Ty_Var (tvdecl_name XK))
                        (map Ty_Var (map tvdecl_name YKs))))                        cs then
                      match kind_check (fromDecl XK :: rev (map fromDecl YKs) ++ drop_Δ' Δ0 [tvdecl_name XK])
                        (Ty_Apps (Ty_Var (tvdecl_name XK)) (map Ty_Var (map tvdecl_name YKs)))
                      with | Some Kind_Base => true | _ => false end else false) = true).
                      {
                        eapply IHcs.
                        intros.
                        eapply c. apply in_cons. auto.
                        auto.
                      }
        destruct_match.
        auto.
          }
        rewrite H0.
        eapply kind_checking_complete in y.
        simpl in y.
        rewrite y.
        reflexivity.
    + exfalso.
      subst.
      inversion e; subst.
      apply andb_false_iff in no_dup.
      destruct no_dup as [DupTV | DUPV].
      * apply no_dup_fun_complete in n. simpl in n. destruct_match. rewrite n in DupTV. inversion DupTV.
      * apply no_dup_fun_complete in n0. rewrite n0 in DUPV. inversion DUPV.
    }
    {
      inversion e; subst.
      destruct (in_dec string_dec (tvdecl_name XK) (map tvdecl_name YKs)) eqn:Hindec.
      {
        exfalso.
        inversion n; subst.
        contradiction.
      }


      simpl.
      destruct (no_dup_fun (map tvdecl_name YKs) &&
        no_dup_fun (map vdecl_name cs)) eqn:no_dup.
    + inversion e; subst.
      apply no_dup_fun_complete in n.
      simpl in n.
      destruct_match.
      subst.
      clear e. clear n. clear n0. clear no_dup.
      induction cs; intros.
      -- simpl. eapply kind_checking_complete in y. simpl in y. rewrite y. reflexivity.
      -- assert (allbmap
              (fun c0 : vdecl =>
            constructor_well_formed_check (rev (map fromDecl YKs) ++ Δ0) c0
              (Ty_Apps (Ty_Var (tvdecl_name XK)) (map Ty_Var (map tvdecl_name YKs))))
              (a :: cs) = true).
          {
            eapply andb_true_intro. split.
            eapply constructor_well_formed_complete.
            eapply c. apply in_eq.
            assert ((if
                      allbmap (fun c0 : vdecl =>
                      constructor_well_formed_check (rev (map fromDecl YKs) ++ Δ0) c0 (Ty_Apps (Ty_Var (tvdecl_name XK))
                        (map Ty_Var (map tvdecl_name YKs))))                        cs then
                      match kind_check (rev (map fromDecl YKs) ++ Δ0)
                        (Ty_Apps (Ty_Var (tvdecl_name XK)) (map Ty_Var (map tvdecl_name YKs)))
                      with | Some Kind_Base => true | _ => false end else false) = true).
                      {
                        eapply IHcs.
                        intros.
                        eapply c. apply in_cons. auto.
                        auto.
                      }
        destruct_match.
        auto.
          }
        rewrite H0.
        eapply kind_checking_complete in y.
        simpl in y.
        rewrite y.
        reflexivity.
    + exfalso.
      subst.
      inversion e; subst.
      apply andb_false_iff in no_dup.
      destruct no_dup as [DupTV | DUPV].
      * apply no_dup_fun_complete in n.  simpl in n. destruct_match. rewrite n in DupTV. inversion DupTV.
      * apply no_dup_fun_complete in n0. rewrite n0 in DUPV. inversion DUPV.
    }
Admitted.

Print Assumptions type_checking_complete.

(* Extraction Language Haskell.
Redirect "type_check.hs" Recursive Extraction type_check. *)

(* Compute (type_check nil (cons ((EmptyString, (Ty_App (Ty_Lam EmptyString Kind_Base (Ty_Var EmptyString)) (Ty_Builtin DefaultUniInteger)))) nil) (Var EmptyString)). *)