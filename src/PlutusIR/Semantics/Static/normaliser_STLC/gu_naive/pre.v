From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List AutosubstSsr.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Arith.

From PlutusCert Require Import STLC_named util alpha.alpha freshness alpha_freshness alpha_ctx_sub.



Create HintDb α_eq_db.
Hint Constructors Alpha : α_eq_db.
Hint Resolve alpha_refl : α_eq_db.
Hint Resolve alpha_sym : α_eq_db.
Hint Resolve alpha_trans : α_eq_db.
Hint Constructors AlphaCtxRefl : α_eq_db.
Hint Constructors AlphaVar : α_eq_db.
Hint Constructors αCtxSub : α_eq_db.
Hint Constructors AlphaCtxSym : α_eq_db.
Hint Constructors αCtxTrans : α_eq_db.
Hint Resolve alpha_extend_ids : α_eq_db.
Hint Constructors IdCtx : α_eq_db.
Hint Resolve sym_alpha_ctx_is_sym : α_eq_db.
Hint Resolve sym_alpha_ctx_is_sym : α_eq_db.
Hint Resolve sym_alpha_ctx_left_is_sym  : α_eq_db.


Fixpoint sub (X : string) (U T : term) : term :=
  match T with
  | tmvar Y =>
    if X =? Y then U else tmvar Y
  | @tmlam B Y K1 T' =>
    @tmlam B Y K1 (sub X U T')
  | @tmapp B T1 T2 =>
    @tmapp B (sub X U T1) (sub X U T2)
  | tmbuiltin d => tmbuiltin d
  end.

Inductive step_naive : term -> term -> Set :=
| step_beta (x : string) (A : PlutusIR.kind) (s t : term) :
    step_naive (@tmapp App (@tmlam Lam x A s) t) ( sub x t s)
| step_appL B s1 s2 t :
    step_naive s1 s2 -> step_naive (@tmapp B s1 t) (@tmapp B s2 t)
| step_appR B s t1 t2 :
    step_naive t1 t2 -> step_naive (@tmapp B s t1) (@tmapp B s t2)
| step_abs B x A s1 s2 :
    step_naive s1 s2 -> step_naive (@tmlam B x A s1) (@tmlam B x A s2).

    

Fixpoint subs (sigma : list (string * term)) (T : term) : term :=
  match sigma with
  | nil => T
  | cons (x, t) sigma' => sub x t (subs sigma' T) (* or the other way around?*)
  end.

Lemma single_subs_is_sub X T s :
  subs [(X, T)] s = sub X T s.
Proof.
  simpl. reflexivity.
Qed.



(* parallel subs *)
Fixpoint psubs (sigma : list (string * term)) (T : term) : term :=
  match T with
  | tmvar x => match lookup x sigma with
              | Some t => t
              | None => tmvar x
              end
  | @tmlam B x A s => @tmlam B x A (psubs sigma s)
  | @tmapp B s t => @tmapp B (psubs sigma s) (psubs sigma t)
  | tmbuiltin d => tmbuiltin d
  end.

Lemma single_subs_is_psub X T s :
  psubs [(X, T)] s = sub X T s.
Proof.
  induction s.
  - simpl. destr_eqb_eq X s. reflexivity.
    reflexivity.
  - simpl. f_equal. apply IHs.
  - simpl. f_equal. apply IHs1. apply IHs2.
  - simpl. reflexivity.
Qed.

(* parallel substitution *)

(* Define the rewrite rules *)
Lemma subs_tmapp {B} : forall sigma s1 s2,
  subs sigma (@tmapp B s1 s2) = @tmapp B (subs sigma s1) (subs sigma s2).
Proof.
  intros sigma s1 s2.
  induction sigma as [| [x t] sigma' IHsigma'].
  - reflexivity.
  - simpl. rewrite IHsigma'. reflexivity.
Qed.

Lemma subs_tmlam {B} : forall sigma x A s,
  subs sigma (@tmlam B x A s) = @tmlam B x A (subs sigma s).
Proof.
  intros sigma x A s.
  induction sigma as [| [y t] sigma' IHsigma'].
  - reflexivity.
  - simpl. rewrite IHsigma'. reflexivity.
Qed.

Lemma subs_builtin : forall sigma d,
  subs sigma (tmbuiltin d) = tmbuiltin d.
Proof.
  intros.
  induction sigma as [| [x t] sigma' IHsigma'].
  - reflexivity.
  - simpl. rewrite IHsigma'. reflexivity.
Qed.

Hint Rewrite (@subs_tmapp App) : subs_db.
Hint Rewrite (@subs_tmapp Fun) : subs_db.
Hint Rewrite (@subs_tmapp IFix) : subs_db.
Hint Rewrite (@subs_tmlam Lam) : subs_db.
Hint Rewrite (@subs_tmlam ForAll) : subs_db.

(* Add the lemmas to the hint database *)
Hint Resolve subs_tmapp : subs_db.
Hint Resolve subs_tmlam : subs_db.

(* So sub is also rewritten when rewriting subs *)
Hint Extern 1 => simpl sub : subs_db.

Fixpoint btv_env (sigma : list (string * term)) : list string :=
  match sigma with
  | nil => nil
  | (x, t)::sigma' => (btv t) ++ (btv_env sigma')
  end.

Lemma btv_env_helper (y : string) (t : term) sigma :
  In y (btv t) -> In t (map snd sigma) -> In y (btv_env sigma).
Proof.
Admitted.

Definition set_diff (l1 l2 : list string) : list string :=
  filter (fun x => negb (existsb (String.eqb x) l2)) l1.

Lemma btv_env_extends_to_tv_env x sigma :
  In x (btv_env sigma) -> In x (tv_keys_env sigma).
Admitted.

Lemma ftv_keys_env_extends_to_tv_env x sigma :
  In x (ftv_keys_env sigma) -> In x (tv_keys_env sigma).
Admitted.


Lemma ftv_keys_env__no_keys sigma x :
  ~ In x (ftv_keys_env sigma) -> ~ In x (map fst sigma).
Admitted.

Lemma ftv_keys_env__no_values sigma x :
  ~ In x (ftv_keys_env sigma) -> (forall val, In val (map snd sigma) -> ~ In x (ftv val)).
Admitted.

(* If x not a key or value, then not both*)
Lemma ftv_keys_env_helper sigma x :
  ~ In x (map fst sigma) -> (forall ftvs, In ftvs (map snd sigma) -> ~ In x (ftv ftvs)) 
    -> ~ In x (ftv_keys_env sigma).
Admitted.


Lemma subs_does_not_create_btv sigma x s :
  ~ In x (btv s) -> ~ In x (btv_env sigma) -> ~ In x (btv (subs sigma s)).
Admitted.

Lemma in_btv_psubs_then_in_constituents x sigma s :
  In x (btv (psubs sigma s)) -> In x (btv s) \/ (exists t, In t (map snd sigma) /\ In x (btv t)).
Proof.
Admitted.

Lemma in_btv_subs_then_in_constituents x sigma s :
  In x (btv (subs sigma s)) -> In x (btv s) \/ (exists t, In t (map snd sigma) /\ In x (btv t)).
Proof.
  
Admitted.

Lemma not_in_constitutents_then_not_in_ftv_psubs x sigma s :
  ~ In x (ftv s) -> ~ In x (flat_map ftv (map snd sigma)) -> ~ In x (ftv (psubs sigma s)).
Proof.
Admitted.

Lemma btv_env_subset a sigma' sigma :
  incl sigma' sigma ->
  ~ In a (btv_env sigma) -> ~ In a (btv_env sigma').
Admitted.

Inductive GU : term -> Set :=
| GU_var x : GU (tmvar x)
(* in app, if s and t do not share GU_vars: *)
| GU_app {B} s t : 
    GU s -> 
    GU t -> 
    forall (H_btv_btv_empty : forall x, In x (btv t) -> ~ In x (tv s)), (* This says disjoint! *)
    forall (H_btv_ftv_empty : forall x, In x (btv s) -> ~ In x (tv t)),
    GU (@tmapp B s t)
| GU_lam {B} x A s : 
    GU s -> 
    ~ In x (btv s) ->
    GU (@tmlam B x A s)
| GU_builtin d :
    GU (tmbuiltin d).

(* Not sure how to call this yet.
if we have NC t sigma
We want to have unique binders elementwise in sigma.
No binder in t can occur as free or bound variable in sigma,
  thus substituting sigma in t will not cause unwanted capture.
*)
Inductive NC : term -> list (string * term) -> Set :=
| nc_nil s :
    NC s []
| nc_cons s x t sigma :
    NC s sigma ->
    (forall y, In y (btv s) -> ((y <> x) * (~ In y (ftv t)))) -> (* no capturing *)
    NC s ((x, t) :: sigma).

Lemma nc_smaller {s sigma x t} : NC s ((x, t)::sigma) -> NC s sigma.
Proof.
  intros.
  inversion H; subst.
  auto.
Qed.

(* why doesnt sigma grow???
  NC: forall btv in s, not in sigma
  we remove a binder, thenw e should still have that all remaining btvs are not in the original sigma.
*)
Lemma nc_lam {B x s A sigma} : 
  NC (@tmlam B x A s) sigma -> NC s sigma.
Proof.
  induction sigma; [constructor|]; intros Hnc.
  inversion Hnc; subst.
  constructor.
  + eapply IHsigma. auto.
  + intros y H_btvs.
    eapply btv_c_lam in H_btvs; eauto.
Qed.

Lemma nc_app_l {B s t sigma} :
  NC (@tmapp B s t) sigma -> NC s sigma.
Proof.
  induction sigma; [constructor|]; intros Hnc.
  inversion Hnc; subst.
  constructor.
  + eapply IHsigma. auto.
  + intros y H_btvs.
    eapply btv_c_appl in H_btvs; eauto.
Qed.

Lemma nc_app_r {B s t sigma} :
  NC (@tmapp B s t) sigma -> NC t sigma.
Proof.
  induction sigma; [constructor|]; intros Hnc.
  inversion Hnc; subst.
  constructor.
  + eapply IHsigma. auto.
  + intros y H_btvs.
    eapply btv_c_appr in H_btvs; eauto.
Qed.

(* No free vars are changed *)
Lemma alpha_preserves_nc_ctx s x t t':
   Alpha [] t t' -> NC s ((x, t)::nil) -> NC s ((x, t')::nil).
Proof.
  intros Ha_t Hnc_t.
  inversion Hnc_t; subst.
  constructor. auto.
  intros y Hbtv.
  specialize (H4 y Hbtv).
  destruct H4 as [Hynotx Hftv_t].
  split; auto.
  eapply alpha_preserves_no_ftv; eauto.
  constructor.
Qed.

Lemma sub_helper {x t s} :
  ~ In x (ftv t) -> ~ In x (ftv (sub x t s)).
Proof.
  intros Hcontra.
  induction s.
  - destr_eqb_eq x s.
    + simpl. destr_eqb_eq s s. auto. contradiction.
    + simpl. destr_eqb_eq x s. auto.
      intros Hcontra2.
      apply ftv_var in Hcontra2. contradiction.
  - simpl. (* remove_string_dec s (ftv (sub x t s0)) is a subset of ftv (sub x t s0)*)
    intros Hcontra2.
    apply in_remove in Hcontra2.
    destruct Hcontra2 as [Hcontra2 _].
    contradiction.
  - simpl. apply not_in_app. split.
    + apply IHs1.
    + apply IHs2.
  - simpl. auto.
Qed.


Lemma subs_does_not_create_ftv sigma x s :
  ~ In x (ftv s) -> ~ In x (ftv_keys_env sigma) -> ~ In x (ftv (subs sigma s)).
Proof.
  intros Hftv_s Hftv_sigma.
  induction s.
  - apply not_in_ftv_var in Hftv_s.
    induction sigma.
    + simpl. unfold not. intros Hcontra.
      destruct Hcontra.
      * symmetry in H. contradiction.
      * contradiction.
    + simpl. destruct a as [y t].
      simpl in Hftv_sigma.
      apply de_morgan2 in Hftv_sigma.
      destruct Hftv_sigma as [ _ Hftv_sigma ].
      apply not_in_app in Hftv_sigma.
      destruct Hftv_sigma as [Hftv_sigma].
      specialize (IHsigma H).
      destr_eqb_eq x y.
      * apply sub_helper. auto.
      * 
        (* This should be its own lemma, since it is about sub now, not subs*)
        {
        induction (subs sigma (tmvar s)).
        - simpl. destr_eqb_eq y s0; auto.
        - simpl.
          intros Hcontra.
          apply in_remove in Hcontra as [Hcontra Hcontra_s0].
          contradiction IHt0.
          eapply ftv_lam_negative; eauto.
        - simpl.
          apply not_in_app. split.
          + apply IHt0_1. auto. eapply not_ftv_app_not_left; eauto.
          + apply IHt0_2. auto. eapply not_ftv_app_not_right; eauto.
        - auto.

        }
        


  - rewrite subs_tmlam.
    destr_eqb_eq x s.
    + apply ftv_lam_no_binder.
    + intros Hcontra.
      apply ftv_lam_helper in Hcontra.
      apply ftv_lam_negative in Hftv_s.
      specialize (IHs Hftv_s).
      contradiction. auto.
  - rewrite subs_tmapp.
    simpl.
    apply not_in_app. split.
    + apply IHs1. auto. eapply not_ftv_app_not_left; eauto.
    + apply IHs2. auto; eapply not_ftv_app_not_right; eauto.
  - rewrite subs_builtin. auto.
Qed.

Lemma step_naive_preserves_no_ftv x t1 t2 :
  step_naive t1 t2 -> ~ In x (ftv t1) -> ~ In x (ftv t2).
Proof.
  intros Hstep Hftv_t1.
  induction Hstep.
  - destr_eqb_eq x x0.
    + apply sub_helper. apply not_ftv_app_not_right in Hftv_t1. auto.
    + rewrite <- single_subs_is_sub.
      apply subs_does_not_create_ftv.
      * apply not_ftv_app_not_left in Hftv_t1. auto. eapply ftv_lam_negative; eauto.
      * unfold ftv_keys_env. simpl. apply not_in_cons. split.
        -- auto.
        -- apply not_ftv_app_not_right in Hftv_t1. rewrite app_nil_r. auto.
  - specialize (IHHstep (not_ftv_app_not_left Hftv_t1)).
    intros Hcontra.
    simpl in Hcontra.
    apply in_app_or in Hcontra.
    destruct Hcontra.
    + apply IHHstep in H.
      contradiction.
    + apply not_ftv_app_not_right in Hftv_t1.
      contradiction.
  - specialize (IHHstep (not_ftv_app_not_right Hftv_t1)).
    intros Hcontra.
    simpl in Hcontra.
    apply in_app_or in Hcontra.
    destruct Hcontra.
    + apply not_ftv_app_not_left in Hftv_t1.
      contradiction.
    + apply IHHstep in H.
      contradiction.
  - destr_eqb_eq x0 x.
    + apply ftv_lam_no_binder.
    + intros Hcontra.
      apply ftv_lam_helper in Hcontra.
      apply ftv_lam_negative in Hftv_t1.
      specialize (IHHstep Hftv_t1).
      contradiction. auto.   
Qed.

Lemma step_naive_preserves_nc_ctx s t1 t2 x :
  step_naive t1 t2 -> NC s ((x, t1)::nil) -> NC s ((x, t2)::nil).
Proof.
  intros Hstep Hnc.
  inversion Hnc; subst.
  constructor.
  - constructor.
  - intros y Hbtv.
    specialize (H4 y Hbtv).
    destruct H4 as [Hynotx Hftv_t].
    split; auto.
    eapply step_naive_preserves_no_ftv. eauto. auto.
Qed.

Lemma gu_app_l {B s t} :
  GU (@tmapp B s t) -> GU s.
Proof.
  inversion 1; auto.
Qed.

Lemma gu_app_r {B s t} :
  GU (@tmapp B s t) -> GU t.
Proof.
  inversion 1; auto.
Qed.

Lemma gu_lam {B x A s} :
  GU (@tmlam B x A s) -> GU s.
Proof.
  inversion 1; auto.
Qed.

Lemma gu_applam_to_nc {BA} {BL} s t x A :
  GU (@tmapp BA (@tmlam BL x A s) t) -> NC s [(x, t)].
Proof.
  intros Hgu.
  inversion Hgu as [ | ? ? ? Hgu_lam Hgu_t Hgu_P1 Hgu_P2 | | ]; subst.
  repeat constructor.
  - intros Hcontra; subst.
    inversion Hgu_lam; subst.
    contradiction.
  - intros Hcontra; apply extend_ftv_to_tv in Hcontra; revert Hcontra.
    apply Hgu_P2.
    apply btv_c_lam; auto.
Qed.

(* The fundamental NC property*)
Lemma nc_ftv_env s sigma :
  NC s sigma -> forall x, In x (btv s) -> ~ In x (ftv_keys_env sigma).
Proof.
  intros Hnc x Hin_btvs.
  induction Hnc.
  - simpl. auto.
  - simpl.
    specialize (p x Hin_btvs) as [Hnotx Hnott].
    apply de_morgan2.
    split; auto.
    apply not_in_app.
    split; auto.
Qed.


Lemma gu_ftv_then_no_btv s x :
  GU s -> In x (ftv s) -> ~ In x (btv s).
Proof.
  intros Hgu Hins.
  induction Hgu.
  - simpl in Hins. auto.
  - simpl in Hins.
    apply in_app_iff in Hins as [Hins | Hins].
    + simpl.
      apply not_in_app.
      split.
      * auto.
      * intros Hcontra.
        apply H_btv_btv_empty in Hcontra.
        apply extend_ftv_to_tv in Hins.
        contradiction.
    + simpl.
      apply not_in_app.
      split.
      * intros Hcontra.
        apply H_btv_ftv_empty in Hcontra.
        apply extend_ftv_to_tv in Hins.
        contradiction.
      * auto.
  - simpl.
    apply de_morgan2.
    split.
    + intros Hcontra.
      subst.
      apply ftv_lam_no_binder in Hins. 
      auto.
    + apply IHHgu.
      apply ftv_lam_helper in Hins.
      auto.
  - inversion Hins.
Qed.



(* Two properties: stopping clash between sigma and s:
  forall x binder in sigma, we rename it in t, hence we need to add that name to R.
  Hence it cannot be free in s, otherwise we no longer have R ⊢ s ~ s.
  We use tv instead of ftv because that decomposes over lam, while we still allow identity substitutions

  Second property: when x is a btv in sigma, then it is not an ftv in sigma.
    e.g. if x is a binder, then we need to rename that in t.
      so then we dont want that same x to also occur free (or as key) in sigma, because then we no longer have
      R ⊢ sigma ~ sigma

    Since identity substitutions have no binders, this still allows for identity substitutions.
    In the lam case we extend sigma with (X, t').
      - X: X was a binder in s, hence a tv in s. So it was not in btv_env_sigma by first condition
      - t': we have control over binders in t', so that is no problem. But for all other binders already in sigma,
            we also need that they don't clash with ftvs in t'. But this is exactly what we are renaming in t':
              those ftv in t' that are binders in sigma! 

    This argument is tooooo subtle, need to formalise.
    What about ftv in t that are also ftv in s? they are not renamed and thus in t'.
     Can they be btv in sigma? No by the first argument

*)

Fixpoint fresh18 (l : list string) : string :=
  match l with
    | nil => "fr"
    | x :: xs => x ++ fresh18 xs
  end.


(* Property that allows to add binder names (a, b, c,...) to alpha context R, and keeping the property that
    R ⊢ s ~ s, and R ⊢ sigma ~ sigma
   - binders in sigma are not free in s
   - binders in sigma are not free in sigma
   - binders in s are not free in sigma, exactly NC s sigma: so moved out of this
*)
Definition Uhm sigma s := ((forall x, In x (btv_env sigma) -> ~ In x (tv s)) 
  * (forall x, In x (btv_env sigma) -> ~ In x (ftv_keys_env sigma)))%type.

Lemma uhm_smaller {sigma s x t} : Uhm ((x, t)::sigma) s -> Uhm sigma s.
Proof.
  intros.
  unfold Uhm.
  split; unfold Uhm in H; destruct H as [ uhm1 uhm2]; intros.
  - eapply uhm1.
    simpl. apply in_app_iff. right. assumption.
  - assert (~ In x0 (ftv_keys_env ((x, t)::sigma))).
    {
      eapply uhm2.
      simpl. apply in_app_iff. right. assumption.
    }
    simpl in H0.
    intuition.
Qed.


Lemma Uhm_appl {B s t sigma} :
  Uhm sigma (@tmapp B s t) -> Uhm sigma s.
Proof.
  intros.
  unfold Uhm in H.
  destruct H as [ uhm1 uhm2].
  unfold Uhm.
  split; intros.
  - specialize (uhm1 x H).
    apply not_tv_dc_appl in uhm1. auto.
  - specialize (uhm2 x H). auto.
Qed.

Lemma Uhm_appr {B s t sigma} :
  Uhm sigma (@tmapp B s t) -> Uhm sigma t.
Proof.
  intros Huhm.
  unfold Uhm in Huhm.
  destruct Huhm as [ uhm1 uhm2].
  unfold Uhm.
  split; intros.
  - specialize (uhm1 x H).
    apply not_tv_dc_appr in uhm1. auto.
  - specialize (uhm2 x H). auto.
Qed.

(* x not in btv s, hence we can add it freely as ftv to sigma*)
Lemma Uhm_lam_id {B x A s sigma} :
  GU (@tmlam B x A s) ->
  (* cannot combine uhm3 and uhm1: free vars in t can still be free vars in s*)
  Uhm sigma (@tmlam B x A s) -> Uhm ((x, tmvar x)::sigma) s.
Proof.
  intros Hgu Huhm.
  unfold Uhm in Huhm.
  destruct Huhm as [ uhm1 uhm2].
  unfold Uhm.
  split; intros.
  - eapply not_tv_dc_lam.
    eapply uhm1. auto.
  - simpl in H.
    simpl.
    apply de_morgan2.
    split; [|apply de_morgan2; split].
    all: try solve [intros Hcontra; subst; apply uhm1 in H; simpl in H; intuition].
    now apply uhm2.
Qed.
