From Equations Require Import Equations.
Require Import PlutusCert.PlutusIR.
Require Import Strings.String.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.

Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Import List.
Import ListNotations.
From PlutusCert Require Import Analysis.FreeVars.
Import Ty.
Require Import Bool.

From Autosubst Require Import Autosubst.

Require Import Lia.

Open Scope string_scope.

(* Type equality *)
Reserved Notation "T1 '=b' T2" (at level 40).
Inductive EqT : ty -> ty -> Prop :=
  (* Beta-reduction *)
  | Q_Beta : forall X K T1 T2 T1',
      substituteTCA X T2 T1 = T1' ->
      Ty_App (Ty_Lam X K T1) T2 =b T1'
  (* Reflexivity, Symmetry and Transitivity*)
  | Q_Refl : forall T,
      T =b T
  | Q_Symm : forall T S,
      T =b S ->
      S =b T
  | Q_Trans : forall S U T,
      S =b U ->
      U =b T ->
      S =b T
  (* Congruence *)
  | Q_Fun : forall S1 S2 T1 T2,
      S1 =b S2 ->
      T1 =b T2 ->
      Ty_Fun S1 T1 =b Ty_Fun S2 T2
  | Q_Forall : forall X K S T,
      S =b T ->
      Ty_Forall X K S =b Ty_Forall X K T
  | Q_Lam : forall X K S T,
      S =b T ->
      Ty_Lam X K S =b Ty_Lam X K T
  | Q_App : forall S1 S2 T1 T2,
      S1 =b S2 ->
      T1 =b T2 ->
      Ty_App S1 T1 =b Ty_App S2 T2
  | Q_IFix : forall F1 F2 T1 T2,
      F1 =b F2 ->
      T1 =b T2 ->
      Ty_IFix F1 T1 =b Ty_IFix F2 T2
where "T1 '=b' T2" := (EqT T1 T2).

#[export] Hint Constructors EqT : core.

(** Normal types *)
Inductive normal_Ty : ty -> Prop :=
  | NO_TyLam : forall bX K T,
      normal_Ty T ->
      normal_Ty (Ty_Lam bX K T)
  | NO_neutral : forall T,
      neutral_Ty T ->
      normal_Ty T
  | NO_TyFun : forall T1 T2,
      normal_Ty T1 ->
      normal_Ty T2 ->
      normal_Ty (Ty_Fun T1 T2)
  | NO_TyForall : forall bX K T,
      normal_Ty T ->
      normal_Ty (Ty_Forall bX K T)
  | NO_TyIFix : forall F T,
      normal_Ty F ->
      normal_Ty T ->
      normal_Ty (Ty_IFix F T)
  | NO_TyBuiltin : forall st,
      normal_Ty (Ty_Builtin st)

with neutral_Ty : ty -> Prop :=
  | NE_TyVar : forall X,
      neutral_Ty (Ty_Var X)
  | NE_TyApp : forall T1 T2,
      neutral_Ty T1 ->
      normal_Ty T2 ->
      neutral_Ty (Ty_App T1 T2).


Fixpoint is_neutral_Ty (t : ty) : bool :=
  match t with
  | Ty_Var _ => true
  | Ty_App T1 T2 => is_neutral_Ty T1 && is_normal_Ty T2
  | _ => false
  end
with is_normal_Ty (t : ty) : bool :=
  match t with
  | Ty_Lam _ _ T => is_normal_Ty T
  | Ty_Fun T1 T2 => is_normal_Ty T1 && is_normal_Ty T2
  | Ty_Forall _ _ T => is_normal_Ty T
  | Ty_IFix F T => is_normal_Ty F && is_normal_Ty T
  | Ty_Builtin _ => true
  (* Cannot call is_neutral on t directly, as it is a mutual recursion *)
  | Ty_App T1 T2 => is_neutral_Ty T1 && is_normal_Ty T2 
  | Ty_Var _ => true
  end.

Scheme normal_Ty__ind := Minimality for normal_Ty Sort Prop
  with neutral_Ty__ind := Minimality for neutral_Ty Sort Prop.

Combined Scheme normal_Ty__multind from
  normal_Ty__ind,
  neutral_Ty__ind.

#[export] Hint Constructors normal_Ty neutral_Ty : core.

(** Type normalisation *)
Inductive normalise : ty -> ty -> Prop :=
  | N_BetaReduce : forall bX K T1 T2 T1n_body T2n T,
      normalise T1 (Ty_Lam bX K T1n_body) ->
      normalise T2 T2n ->
      normalise (substituteTCA bX T2n T1n_body) T ->
      normalise (Ty_App T1 T2) T
  | N_TyApp : forall T1 T2 T1n T2n,
      normalise T1 T1n ->
      neutral_Ty T1n -> (* Idea: Remove this and show SN for that? *)
      normalise T2 T2n ->
      normalise (Ty_App T1 T2) (Ty_App T1n T2n)
  | N_TyFun : forall T1 T2 T1n T2n,
      normalise T1 T1n ->
      normalise T2 T2n ->
      normalise (Ty_Fun T1 T2) (Ty_Fun T1n T2n)
  | N_TyForall : forall bX K T0 T0n,
      normalise T0 T0n ->
      normalise (Ty_Forall bX K T0) (Ty_Forall bX K T0n)
  | N_TyLam : forall bX K T0 T0n,
      normalise T0 T0n -> (* TODO: Why do we "evaluate" the inside of the lambda? Isn't a lambda "a value"?*)
      normalise (Ty_Lam bX K T0) (Ty_Lam bX K T0n)
  | N_TyVar : forall X,
      normalise (Ty_Var X) (Ty_Var X)
  | N_TyIFix : forall F T Fn Tn,
      normalise F Fn ->
      normalise T Tn ->
      normalise (Ty_IFix F T) (Ty_IFix Fn Tn)
  | N_TyBuiltin : forall st,
      normalise (Ty_Builtin st) (Ty_Builtin st)
  .

#[export] Hint Constructors normalise : core.

(* Module Normalisation.

Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation multistep := (multi normalise).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(* TODO: I think the stability lemmas below already show this *)
Lemma normalise_refl : forall ty1,
  normal_Ty ty1 -> normalise ty1 ty1.
Proof.
Admitted.


Definition halts (t : ty) : Prop := exists t', and (t -->* t') (normal_Ty t').

Definition env := list (string * ty).

Fixpoint msubst (delta : env) (t : ty) : ty :=
  match delta with
  | [] => t
  | (X, T) :: delta' => msubst delta' (substituteTCA X T t)
  end.

Definition tass := list (string * kind).

Fixpoint mupdate (new_values : list(string * kind)) (Delta : list (string * kind)) :=
  match new_values with
  | [] => Delta
  | ((X, K) :: xs) => (X, K) :: mupdate xs Delta
  end.

Lemma mupdate_right_identity : forall (new_values : list(string * kind)),
  mupdate new_values [] = new_values.
Proof.
Admitted.

Lemma Ty_Lam_normalization : forall X K1 delta T t,
  msubst delta T -->* t ->
  Ty_Lam X K1 (msubst delta T) -->* Ty_Lam X K1 t.
Proof.
  intros X K1 delta T t Hnorm.
  induction Hnorm.
  - apply multi_refl. 
  - apply multi_step with (y := Ty_Lam X K1 y).
    + apply N_TyLam.
      assumption.
    + assumption.
Qed.


Fixpoint SN kind ty : Prop :=
  and (and ([] |-* ty : kind) (halts ty))
  match kind with
  | Kind_Base => True
  | Kind_Arrow k1 k2 => forall ty', SN k1 ty' -> SN k2 (Ty_App ty ty')
  end.

Inductive instantiation : tass -> env -> Prop :=
| V_nil :
    instantiation nil nil
| V_cons : forall x kind ty c e,
    normal_Ty ty -> SN kind ty ->
    instantiation c e ->
    instantiation ((x,kind)::c) ((x,ty)::e).

Lemma SN_implies_halts : forall {kind} {ty},
  SN kind ty -> halts ty.
Proof.
  intros kind ty H.
  destruct kind. (* TODO: Why is this destructuring necessary? *)
  - destruct H as [[_ Hhalts] _]; assumption.
  - destruct H as [[_ Hhalts] _]; assumption. 
Qed.

(* Substituting type variables does not change kind*)
Lemma msubst_preserves_kinding : forall new_values delta,
  instantiation new_values delta ->
  forall Delta ty kind,
  mupdate new_values Delta |-* ty : kind ->
  Delta |-* (msubst delta ty) : kind.
Proof.
Admitted.



(* TODO: I don't know if this is true, and everything hinges on this lemma *)
(* I think it makes sense though.*)
(* It does not make sense, because x becomes a free variable in T, and SN is only
   defined for empty contexts *)
(* But it does make sense if SN subst x ty T implies halts T. *)
Lemma substituteTCA_SN_preserves_halts : forall K K' x ty T,
  [] |-* ty : K' -> SN K' ty -> 
  
  SN K (substituteTCA x ty T) -> halts T.
Proof.
  intros K K' x ty T Hkind HSNK' HSNsubst.
  induction T.
  - (* Ty_Var *)
    funelim (substituteTCA x ty (Ty_Var t)); try discriminate.
    destruct Heqcall.
    (* true without assumptions I think ?? *)
    admit.
    
  - shelve.
  - shelve.
  - shelve.
  - shelve.
  - (* Ty_Lam *)
    (* We know K is of the form _ -> _ *)
   (* Ty_App *)
Admitted.
  
Corollary msubst_SN_preserves_halts : forall K x ty T delta,
  SN K (msubst ((x, ty)::delta) T) -> halts T.
Proof.
Admitted.




(* no free vars in closed terms*)
Definition closed (t:ty) :=
  forall x, not (In x (Ty.ftv t)).

Fixpoint closed_env (env:env) :=
  match env with
  | nil => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.

(* Properties of Instantiations *)
Lemma instantiation_domains_match: forall {c} {e},
    instantiation c e ->
    forall {x} {K},
      List.lookup x c = Some K -> exists ty, List.lookup x e = Some ty.
Proof.
Admitted.

(* By the definition of instantiation, all (ty, kind) pairs in instantiation are strongly normalizing *)
Lemma instantiation_SN : forall c e,
    instantiation c e ->
    forall x T K,
      List.lookup x c = Some K ->
      List.lookup x e = Some T -> SN K T.
Proof.
Admitted.

Lemma instantiation_env_closed : forall c e,
  instantiation c e -> closed_env e.
Proof.
Admitted.


(* Properties of multi-substitutions *)

Lemma msubst_var: forall ss x, 
  closed_env ss -> msubst ss (Ty_Var x) =
  match List.lookup x ss with
  | Some t => t
  | None => Ty_Var x
end.
Proof.
  (* TODO: See why the closed_env requirement is there*)
Admitted.

(* TODO: Is that true with fresh stuff and all? *)
(* I would say it is true "enough"*)
Lemma msubst_lam : forall delta X K1 T,
  msubst delta (Ty_Lam X K1 T) = Ty_Lam X K1 (msubst delta T).
Proof.
Admitted.



Lemma normalise_preserves_SN : forall K ty ty', 
(normalise ty ty') -> SN K ty' -> SN K ty.
Proof.
Admitted.
Lemma multistep_preserves_SN : forall K ty ty', 
ty -->* ty' -> SN K ty' -> SN K ty.
Proof.
Admitted.
Lemma multistep_preserves_SN' : forall K ty ty',
ty -->* ty' -> SN K ty -> SN K ty'.
Proof.
Admitted.



Lemma construct_ty_SN : forall K,
  exists v, and (normal_Ty v ) (SN K v).
Proof.
  intros K.
  induction K.
  - exists (Ty_Builtin (Some' (TypeIn DefaultUniInteger))).
    split.
    + apply NO_TyBuiltin.
    + unfold SN.
      split; [split|].
      * apply K_Builtin.
        apply K_DefaultUniInteger.
      * unfold halts.
        exists (Ty_Builtin (Some' (TypeIn DefaultUniInteger))).
        split. 
        -- apply multi_refl.
        -- apply NO_TyBuiltin.
      * reflexivity.
  - destruct IHK1 as [ty1 H1].
    destruct IHK2 as [ty2 H2].
    exists (Ty_Lam "x" K1 ty2). (* MEETING: Maybe we need to make "x" so that x not in anything, i.e. fresh. NOt possible I think, needs to work for arbitrary ty2?*)
    split.
    + apply NO_TyLam.
      destruct H2.
      assumption.
    + unfold SN; split; [split|fold SN]. (* TODO ask, shouldn't we get an induction hypothesis here?*)
      * apply K_Lam.
        destruct H2.
        induction K2; unfold SN; destruct H0 as [[H0 _] _ ]; admit. (* and then weakening, done*)
        
      * unfold halts.
        exists (Ty_Lam "x" K1 ty2).
        split.
        apply multi_refl.
        apply NO_TyLam. destruct H2 as [H2 _].
        assumption.
        
      *
        intros ty' Hty'.
        
        
        destruct H2 as [H2norm H2SN].
        admit.
        (* Big question: Do we have SN K2 ty2 /\ SN K1 ty' => SN K2 ("x" -> ty') ty2*)
          (* Maybe we can conclude from SN K2 ty2, that "x" is not free in ty2??, yes we can!*)
          (* Then ("x" -> ty') ty2 = ty2, and it holds!*)
          (* Use typable_empty, closed definition, and substituteTCA definition (("x" -> ty') ty2 = ty2 may only hold up to renaming!)*)
          (* NOTE: This does not hold anymore if we change the logical relation to be more generic and have open kinding relations*)
          (* Renaming remark should be good, because "if existsb (eqb Y) (ftv U)", with U=ty' is always false*)
          (* Because ftv U = [], since [] |-* ty' : K1 by SN K1 ty'*)

Admitted.

Lemma well_kinded_subst_implies_SN : forall c ty kind delta,
  c |-* ty : kind -> 
  instantiation c delta ->
  SN kind (msubst delta ty).
Proof.
  intros c ty kind delta Hwk V. 
  generalize dependent delta. (* Not needed for TyVar, maybe for the others?  *)
  induction Hwk; intros.
  - destruct (instantiation_domains_match V H) as [t P].
    assert (V' := V).
    apply instantiation_SN with (x := X) (T := t) (K := K) in V; auto.
    rewrite msubst_var; admit.
    (* + rewrite P. assumption.
    + apply instantiation_env_closed with (c := Δ) (e := delta).
      assumption. *)
    
     
  - shelve.
  - shelve.
  - shelve.
  - shelve.
  - (* NOTE: Why don´t we have ((X, K1) :: Delta) |-* T : K2 AND 
        instantiation ((X, K1) :: Delta) delta -> SN K2 (msubst delta T)   
        INSTEAD OF  what we have now, where ((X, K1) :: Delta) |-* T : K2   
        is already known and not a precondition anymore???*)
    unfold SN. fold SN.
    
    
    
    split; [split|].
    
    + apply msubst_preserves_kinding with (new_values := Δ); [assumption|].
      rewrite mupdate_right_identity.
      apply K_Lam.
      assumption.
    + rewrite msubst_lam.
      apply K_Lam in Hwk. (* Idea is that msubst only substitutes SN terms (by V : instantiation Δ delta) I think, which halt, so the whole should halt*)
      pose proof (construct_ty_SN K1) as Existence_ty.
      destruct Existence_ty as [my_ty [Hnormal HSN]].
      assert (instantiation ((X, K1) :: Δ) ((X, my_ty) :: delta)) as V'.
      {
        apply V_cons; assumption. (* by construction *)
      }
      apply (IHHwk ((X, my_ty) :: delta)) in V'.
      simpl in V'.
      apply SN_implies_halts in V'.
      assert (halts (msubst delta T)) by admit. (* This should be true. Leaving out a substitution should not make normalizing 'harder'*)

      
       
      (* apply SN_implies_halts in V'. *)

      (* halts T -> halts Ty_Lam _ _ T*)
      unfold halts.
      unfold halts in H.
      destruct H as [t* [Hnorm HnormalTy]].
      exists (Ty_Lam X K1 t).
      split.
      * apply Ty_Lam_normalization.
        assumption. 
      * apply NO_TyLam.
        assumption.
    + 
      (* Above I showed (msubst delta (Ty_Lam X K1 T) -->* v=(Ty_Lam X K1 v'))*)
      (* ANd with new existential SN definition, we then need to show
         SN K2 ((\X:K1 . v') ty') 
         Which should be the same as proving
         SN K2 [X -> ty']v'.
         This looks kind of like SN K2 (msubst (X, ?)::delta  T).
         In the halts case we constructed a ty like that, but now we actually need to have
         that it holds for all ty? So SN K2 (msubst (X, ty')::delta)
         But we have the additional condition SN K1 ty'.
          Is that enough to show that value ty' /\ SN K1 ty', by the instantiation definition?
          SN K1 ty' is direct from the condition. But value ty'?
          No, value ty' is not always true. Why do we need this condition?
          We needed it because we ended up in a form SN K2 [X -> ty']v' and we wanted to be able to
          say something about that from IHHwk's result: SN K2 [X |-> ?] T
            SO solution: First evalute ty' to a value v_ty'.
              ( this was already necessary to do the beta reduction step according to our operational semantics)
          -----
          So starting over (ignoring other substitutions in original Delta/delta): 
          We need to show forall ty'
            SN K2 [X -> v_ty']v', where ty' -->* v_ty' /\ value v_ty' (which exists by SN K1 ty').
              which we can show using IHHwk, by setting delta = (X, v_ty')::delta, so then
              we need to show:
            instant ((X, K1)::Delta) ((X, v_ty')::delta), 
              which by instantiation Delta delta means showing  
            value v_ty' /\ SN K1 v_ty',
              of which the first is true by construction, so
            SN K1 v_ty' =>
              YES, BY MULTISTEP_PRESERVES_R'!!!!!!!!

          Let's step back again:
          By IHHwk with v_ty', we know:
            SN K2 (msubst (X, v_ty')::delta T).
            =???
            SN K2 (msubst (X, v_ty')::(delta-X) T).  (* Ok, back up: I always thought that by adding something onto the substitution list, the previous value would be ignored, but that is not the case actually...*)
                                                    (* Anyways, this should hold, so maybe we have to change the context update definition*)
            

          We need to show that the above results in this below:
            SN K2 (Ty_Lam X K1 v') ty'
            -->*
            SN K2 (Ty_Lam X K1 v') v_ty'.
            -->*
            SN K2 (msubst (X, v_ty')::[] v')   (and msubst (delta-X) T -->* v', so it should be true???).4

            which we can show by showing that
            there exists v'' such that (msubst (X, v_ty')::(delta - X) T) -->* v''
            and msubst (X, v_ty')::[] v' -->* v''.

          That doesnt immediately follow.
          From (msubst delta (Ty_Lam X K1 T) -->* v=(Ty_Lam X K1 v'))
          we can also do it differently:
          msubst delta (Ty_Lam X K1 T) = Ty_Lam X K1 (msubst delta-X T)
            which goes to v if
            msubst delta-X T -->* v'


         *)
        admit.
  - shelve.
Admitted.

Corollary well_kinded_implies_SN : forall ty kind,
  [] |-* ty : kind -> SN kind ty.
Proof.
  (* intros ty kind H.
  apply well_kinded_subst_implies_SN with (Delta := []) (delta := []) in H.
  - simpl in H. 
    assumption. 
  - apply V_nil. 
Qed. *)
Admitted.

(* Main theorem that shows that normalization terminates for well kinded terms*)
Theorem strong_normalization : forall T K,
  [] |-* T : K -> halts T.
Proof.
  (* intros T K H.
  apply SN_implies_halts with (kind := K).
  apply well_kinded_implies_SN.
  assumption.
Qed. *)
Admitted.

End Normalisation.
(* TODO: Use function with measure?
Equations? normalise_check_easy (ty : PlutusIR.ty) : (option PlutusIR.ty) by wf (size ty):=
    (* Simplified version of Ty_App that is enough for the difficult termination proof *)
  normalise_check_easy (Ty_App T1 T2) =>
    match T1 with
    | Ty_Lam bX K T1_body => normalise_check_easy (substituteTCA bX T2 T1_body)
    | _ => if is_neutral_Ty T1 then Some (Ty_App T1 T2) else None
    end;
  normalise_check_easy (Ty_Lam bX K T0) =>
    match normalise_check_easy T0 with
    | Some T0n => Some (Ty_Lam bX K T0n)
    | _ => None
    end;
  normalise_check_easy t => Some t.
Proof.
Abort. *)
  
  
(* Equations normalise_check (ty : PlutusIR.ty) : (option PlutusIR.ty) :=
  (* normalise_check (Ty_App T1 T2) =>
    match normalise_check T1, normalise_check T2 with
    | Some T1n, Some T2n => 
        match T1n with
        | Ty_Lam bX K T1n_body => normalise_check (substituteTCA bX T2n T1n_body)
        | _ => if is_neutral_Ty T1n then Some (Ty_App T1n T2n) else None
        end
    | _, _ => None
    end; *)
  normalise_check (Ty_Fun T1 T2) => 
    match normalise_check T1, normalise_check T2 with
    | Some T1n, Some T2n => Some (Ty_Fun T1n T2n)
    | _, _ => None
    end; 
  normalise_check (Ty_Forall bX K T0) =>
    match normalise_check T0 with
    | Some T0n => Some (Ty_Forall bX K T0n)
    | _ => None
    end;
  normalise_check (Ty_Lam bX K T0) =>
    match normalise_check T0 with
    | Some T0n => Some (Ty_Lam bX K T0n)
    | _ => None
    end;
  normalise_check (Ty_Var X) => Some (Ty_Var X);
  normalise_check (Ty_IFix F T) =>
    match (normalise_check F, normalise_check T) with
    | (Some Fn, Some Tn) => Some (Ty_IFix Fn Tn)
    | (_, _) => None
    end;
  normalise_check (Ty_Builtin st) => Some (Ty_Builtin st);
  normalise_check t => Some t *)
  (* . *)
(* Proof. *)
(* Admitted. *)
(* Abort. *)


(* Theorem normalise_checking_sound : forall ty tyn,
  normalise_check ty = Some tyn -> normalise ty tyn.
Proof.
  intros ty.
  induction ty; intros tyn H.
Admitted.

Theorem normalise_checking_complete : forall ty tyn,
  normalise ty tyn -> normalise_check ty = Some tyn.
Proof.
Admitted. *)
 *)


(** Properties of type normalisation *)
Lemma normalise_to_normal : forall T Tn,
    normalise T Tn ->
    normal_Ty Tn.
Proof.
  induction 1; eauto.
Qed.

Lemma normalisation__deterministic : forall T Tn T'n,
    normalise T Tn ->
    normalise T T'n ->
    Tn = T'n.
Proof.
  intros.
  generalize dependent T'n.
  induction H; intros.
  - inversion H2.
    + subst.
      apply IHnormalise1 in H5. inversion H5. subst.
      apply IHnormalise2 in H6. subst.
      apply IHnormalise3; eauto.
    + subst.
      apply IHnormalise1 in H5.
      inversion H5. subst.
      inversion H6.
  - inversion H2.
    + subst.
      apply IHnormalise1 in H5.
      inversion H5. subst.
      inversion H0.
    + subst.
      f_equal; eauto.
  - inversion H1. subst.
    f_equal; eauto.
  - inversion H0. subst.
    f_equal; eauto.
  - inversion H0. subst.
    f_equal; eauto.
  - inversion H0. subst.
    f_equal; eauto.
  - inversion H1. subst.
    f_equal; eauto.
  - inversion H0. subst.
    eauto.
Qed.

Ltac invert_normalise :=
  match goal with
  | H : normalise ?T ?Tn |- _ => inversion H; subst; f_equal; eauto
  end.

Theorem normalisation__stable :
  (forall T, normal_Ty T -> (forall Tn, normalise T Tn -> T = Tn)) /\
  (forall T, neutral_Ty T -> (forall Tn, normalise T Tn -> T = Tn)).
Proof with eauto.
  eapply normal_Ty__multind; intros...
  all: try solve [invert_normalise].
  - inversion H3.
    + subst.
      eapply H0 in H6.
      subst.
      inversion H.
    + subst.
      f_equal...
Qed.

Corollary normalisation__stable__normal : forall T,
    normal_Ty T ->
    forall Tn,
      normalise T Tn -> T = Tn.
Proof. apply normalisation__stable. Qed.

Corollary normalisation__stable__neutral : forall T,
    neutral_Ty T ->
    forall Tn,
      normalise T Tn -> T = Tn.
Proof. apply normalisation__stable. Qed.

Lemma normalisation__stable' :
  (forall Tn, normal_Ty Tn -> normalise Tn Tn) /\
  (forall Tn, neutral_Ty Tn -> normalise Tn Tn).
Proof. apply normal_Ty__multind; eauto. Qed.

Corollary normalisation__stable'__normal : forall Tn,
    normal_Ty Tn ->
    normalise Tn Tn.
Proof. apply normalisation__stable'. Qed.

Corollary normalisation__stable'__neutral : forall Tn,
    neutral_Ty Tn ->
    normalise Tn Tn.
Proof. apply normalisation__stable'. Qed.

Theorem normalisation__sound : forall T Tn,
    normalise T Tn ->
    T =b Tn.
Proof with eauto. induction 1... Qed.

Lemma normalisation__complete : forall S T Sn,
    S =b T ->
    normalise S Sn ->
    normalise T Sn.
Proof. Abort.

(** Normalisation of lists of types*)
Inductive map_normalise : list (string * ty) -> list (string * ty) -> Prop :=
  | MN_nil :
      map_normalise nil nil
  | MN_cons : forall X T Ts Tn Tsn,
      map_normalise Ts Tsn ->
      normalise T Tn ->
      map_normalise ((X, T) :: Ts) ((X, Tn) :: Tsn).

#[export] Hint Constructors map_normalise : core.

Require Import Coq.Lists.List.
Import ListNotations.

Lemma MN_snoc : forall X T Ts Tn Tsn,
  map_normalise Ts Tsn ->
  normalise T Tn ->
  map_normalise (Ts ++ [(X, T)]) (Tsn ++ [(X, Tn)])
.
Proof.
  induction Ts.
  - simpl.
    induction Tsn.
    + eauto using map_normalise.
    + intros H_problem.
      inversion H_problem.
  - intros.
    inversion H. subst.
    simpl.
    econstructor; eauto.
Qed.

Lemma MN_app Ts Tsn Ts' Tsn' :
  map_normalise Ts Tsn ->
  map_normalise Ts' Tsn' ->
  map_normalise (Ts ++ Ts') (Tsn ++ Tsn').
Proof.
  intros H1 H2.
  induction H1.
  - assumption.
  - simpl.
    constructor; auto.
Qed.


Lemma map_normalise__app : forall l1 l2 ln,
    map_normalise (l1 ++ l2) ln ->
    exists l1n l2n,
      map_normalise l1 l1n /\
      map_normalise l2 l2n /\
      ln = l1n ++ l2n.
Proof.
  induction l1; intros.
  - exists nil. exists ln. eauto.
  - inversion H. subst.
    eapply IHl1 in H2.
    destruct H2 as [l1n' [l2n' [Hmn1 [Hmn2 Heq]]]].
    subst.
    exists ((X, Tn) :: l1n').
    exists l2n'.
    eauto.
Qed.

Lemma map_normalise__deterministic : forall l ln ln',
    map_normalise l ln ->
    map_normalise l ln' ->
    ln = ln'.
Proof with eauto.
  induction l. all: intros.
  all: inversion H.
  all: inversion H0.
  all: subst.
  - reflexivity.
  - inversion H6. subst.
    f_equal.
    + f_equal.
      eauto using normalisation__deterministic.
    + eauto.
Qed.

Axiom norm : ty -> ty.
Axiom norm_normalise : forall ty, normalise ty (norm ty).

Axiom map_norm : list (string * ty) -> list (string * ty).
Axiom map_norm_map_normalise : forall Ts, map_normalise Ts (map_norm Ts).

