From Equations Require Import Equations.
Require Import PlutusCert.PlutusIR.
Require Import Strings.String.
(* Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding. *)

(* Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution. *)
Require Import List.
Import ListNotations.
From PlutusCert Require Import Analysis.FreeVars.
Import Ty.
Require Import Bool.

Require Import Lia.

Open Scope string_scope.

(* Normalisation proof à la Xi and Donnelly *)
(* Uses non-deterministic small step semantics and an implicit value definition *)
(* For now proved for STLC with simple term language *)

(** * Regular substitution of types *)

Inductive tp :=
    | tpbas : tp
    | tpfun : tp -> tp -> tp.

Inductive tps :=
    | tpsnil : tps
    | tpsmore : tps -> tp -> tps.

Inductive tm :=
    | tmvar : nat -> tm
    | tmlam : tm -> tm
    | tmapp : tm -> tm -> tm.

Inductive tmshi : tm -> tm -> nat -> Prop :=
  | TMSHIvargte : forall (i l : nat), i >= l ->
      tmshi (tmvar i) (tmvar (i+1)) l
  | TMSHIvarlt : forall (i l : nat), i < l ->
      tmshi (tmvar i) (tmvar i) l
  | TMSHIlam : forall (t t' : tm) (l : nat),
      tmshi t t' (S l) ->
      tmshi (tmlam t) (tmlam t') l
  | TMSHIapp : forall (t1 t2 t1' t2' : tm) (l : nat),
      tmshi t1 t1' l ->
      tmshi t2 t2' l ->
      tmshi (tmapp t1 t2) (tmapp t1' t2') l.

Inductive tms :=
  | tmsnil : tms
  | tmsmore : tms -> tm -> tms.

Inductive subshi : tms -> tms -> Prop :=
  | SUBSHInil : subshi tmsnil tmsnil
  | SUBSHImore : forall (ts ts' : tms) (t t' : tm),
      subshi ts ts' ->
      tmshi t t' 0 ->
      subshi (tmsmore ts t) (tmsmore ts' t').

Inductive TMI : nat -> tm -> tms -> Type :=
  | TMIone : forall {ts : tms} {t : tm},
      TMI 0 t (tmsmore ts t)
  | TMIshi : forall {ts : tms} {t t' : tm} {i : nat}, i > 0 ->
      TMI (i-1) t ts ->
      TMI i t (tmsmore ts t').

Inductive subst : tms -> tm -> tm -> Prop :=
  | SUBvar : forall (ts : tms) (t : tm) (i : nat),
      TMI i t ts ->
      subst ts (tmvar i) t
  | SUBlam : forall (ts ts' : tms) (t t' : tm),
      subshi ts ts' ->
      subst (tmsmore ts' (tmvar 0)) t t' ->
      subst ts (tmlam t) (tmlam t')
  | SUBapp : forall (ts : tms) (t1 t2 t1' t2' : tm),
      subst ts t1 t1' ->
      subst ts t2 t2' ->
      subst ts (tmapp t1 t2) (tmapp t1' t2').

Definition subst1 (t1 t2 t3 : tm) : Prop :=
  subst (tmsmore tmsnil t1) t2 t3.

Inductive TPI : nat -> tp -> tps -> Type :=
  | TPIone : forall {G : tps} {T : tp},
      TPI 0 T (tpsmore G T)
  | TPIshi : forall {G : tps} {T T' : tp} {i : nat},
      TPI i T G ->
      TPI (S i) T (tpsmore G T').

Inductive DER : tps -> tm -> tp -> nat -> Prop :=
  | DERvar : forall (G : tps) (i : nat) (T : tp),
      TPI i T G -> DER G (tmvar i) T 0

  | DERlam : forall (G : tps) (T1 T2 : tp) (t : tm) (s : nat),
      DER (tpsmore G T1) t T2 s ->
      DER G (tmlam t) (tpfun T1 T2) (S s)

  | DERapp : forall (G : tps) (T1 T2 : tp) (t1 t2 : tm) (s1 s2 : nat),
      DER G t1 (tpfun T1 T2) s1 ->
      DER G t2 T1 s2 ->
      DER G (tmapp t1 t2) T2 (S (s1 + s2)).

(* Assume the necessary definitions for tps, tm, tp, and DER are already in place *)

Definition DER0 (G : tps) (t : tm) (T : tp) : Prop :=
  exists s : nat , DER G t T s.



Inductive RED : tm -> tm -> nat -> Prop :=
  | REDlam : forall (t t' : tm) (s : nat),
      RED t t' s ->
      RED (tmlam t) (tmlam t') (S s)

  | REDapp1 : forall (t1 t2 t1' : tm) (s : nat),
      RED t1 t1' s ->
      RED (tmapp t1 t2) (tmapp t1' t2) (S s)

  | REDapp2 : forall (t1 t2 t2' : tm) (s : nat),
      RED t2 t2' s ->
      RED (tmapp t1 t2) (tmapp t1 t2') (S s)

  | REDapp3 : forall (t v t' : tm),
      subst1 v t t' -> (* Problematic. We cannot reduce (\x. x y) (3) now.*)
      RED (tmapp (tmlam t) v) t' 0.

Definition RED0 (t t' : tm) : Prop :=
  exists s, RED t t' s.

(* Implicitly says that if a term cannot reduce anymore, then it is strongly normalizing
     (possibly with more steps (n) than absolutely necessary)*)
(* Strong Normalization *)
Inductive SN : tm -> nat -> Prop :=
  | SN_intro : forall t n,
      (forall t', RED0 t t' -> exists n', n' < n /\ SN t' n') ->
      SN t n.

Definition SN0 (t : tm) : Prop :=
    exists n : nat, SN t n.

Lemma forwardSN : forall t t' n,
  SN t n -> RED0 t t' -> exists n', n' < n /\ SN t' n'.
Proof.
  intros t t' n sn red.
  inversion sn as [t0 n0 H].
  specialize (H t' red).
  assumption.
Qed.

Lemma backwardSN : forall t,
  (exists t', RED0 t t' /\ SN0 t') -> SN0 t.
Proof.
Admitted.

(* Reducibility *)
Fixpoint R (tm : tm) (T : tp) : Prop :=
    match T with
    | tpbas => SN0 tm
    | tpfun tp1 tp2 => 
      (forall tm', R tm' tp1 -> R (tmapp tm tm') tp2)
    end.

(* Sequence of reducibility predicates for a substitution *)
Inductive RS : tms -> tps -> nat -> Prop :=
  | RSnil : RS tmsnil tpsnil 0
  | RSmore : forall {ts : tms} {t : tm} {G : tps} {T : tp} {n : nat},
      RS ts G n ->
      R t T ->
      RS (tmsmore ts t) (tpsmore G T) (S n).





Definition RS0 (ts : tms) (G : tps) : Type :=
  {n : nat & RS ts G n}.

(* Definition of neutral terms *)
Inductive NEU : tm -> Type :=
  | NEUvar : forall (i : nat), NEU (tmvar i)
  | NEUapp : forall (t1 t2 : tm), NEU (tmapp t1 t2).

Lemma mainLemmaVar : forall {G : tps} {T : tp} {ts : tms} {t : tm} {i : nat}
  (tpi : TPI i T G) (tmi : TMI i t ts) (rs : RS0 ts G),
  R t T.
Proof.
  intros G T ts t i tpi tmi rs.
  destruct tpi as [G T | G T T' i tpi'].
  -  (* Case: TPIone *)
    inversion tmi.
    + subst.
      destruct rs as [n rs].
      clear tmi.
      inversion rs.
      assumption.
    + inversion H.
  - inversion tmi. 
    destruct rs as [n rs].
    subst.
    (* t is the S i - 1 = ith term in ts0, and T is the ith term in G, and RS ts0 G, so easy.*)
Admitted.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Wf_nat.

(* Says: substituting x for x has no effect*)
(* TODO: Should be provable..., but maybe changing the subst 
    definition to capture the subst tmsnil behaviour is better*)
Lemma vacuousSubLemma : forall {t : tm} {T : tp} {s: nat} ,
  DER tpsnil t T s -> subst (tmsmore tmsnil (tmvar 0)) t t.
Proof.
  intros t T s der.
  induction s.
  + admit.
  (* + apply SUBlam with (ts' := (tmsmore tmsnil (tmvar 1))). *)
Admitted.  

(* NOTE: We use inversion der instead of induction der because with induction 
  the var case is not seen as impossible...
  CONSEQUENCE: Now we need this s in the derivation, but we may also be able to use structural induction on der?
  *)
(* NOTE: In the original AST code, this did not have a well-kindedness assumption, but this is necessary for the var case*)
Lemma lemma10 : forall {t : tm } { T : tp} {s : nat},
  DER tpsnil t T s -> subst tmsnil t t.
Proof.
  (* Proof sketch:
      DER tpsnil t T s, so no free vars in t, so it cannot be tmvar
      For lam we get a goal like: subst (tmsmore tmsnil (tmvar 0)) t t, which says: replace (tmvar 0) by (tmvar 0), which shouldnt do anything, so true.

  *)
  intros t T s.
  apply (well_founded_induction lt_wf (fun s => forall T, forall t, DER tpsnil t T s -> subst tmsnil t t)).
  intros x IH.
  intros T0 t0 der.
  inversion der.
  inversion der; try subst; inversion H. (* why does this not use that G=tmsnil???*)

  - apply SUBlam with (ts := tmsnil) (ts' := tmsnil).
    + apply SUBSHInil.
    + apply vacuousSubLemma.
      admit.
  - apply SUBapp. (* induction lemma 10 with smaller s *)
    + specialize (IH s1).
      apply IH with (T := (tpfun T1 T0)).
      * admit. (* Follows from S (s1 + s2) = x*)
      * assumption.
    + specialize (IH s2).
      apply IH with (T := T1).
      * admit. (* Follows from (S (s1 + 2))*)
      * assumption.     
  
Admitted.

Lemma lemma20 :
  forall {ts ts': tms} {t t1 t' t'': tm} ,
    subshi ts ts' ->
    subst (tmsmore ts' (tmvar 0)) t t' ->
    subst1 t1 t' t'' ->
    subst (tmsmore ts t1) t t''.
Proof.
  intros ts ts' t t1 t' t''.
  intros subshi sub sub1.
  (* I thought it was impossible, but it is crucial 
      that t' has no free variables (except for 0), this 
      follows from inversion on subst1*)
Admitted.



(* R is preserved by forward reduction *)
Lemma cr2 : forall (t t' : tm) (tp : tp) (n : nat),
  R t tp -> RED0 t t' -> R t' tp.
Proof.
  (* intros t t' T n r rd.
  generalize dependent t'.
  generalize dependent t.
  induction T; intros t r t' rd; unfold R in r; fold R in r.
  - 
    unfold R.
    unfold SN0 in r.
    destruct r as [n1 r].
    assert (H : exists n', n' < n1 /\ SN t' n').
    {
      apply forwardSN with (t := t) (t' := t') (n := n1).
      - exact r.
      - exact rd.
    }
    destruct H as [n' [_ H]].
    unfold SN0.
    exists n'.
    assumption.
  -
    unfold R; fold R.
    split.
    { (* Proving halting *)
        destruct r as [r _].
        unfold SN0 in r.
        destruct r as [nSn r].
        unfold SN0.
        assert (H : exists n', n' < nSn /\ SN t' n').
        {
        apply forwardSN with (t := t) (t' := t') (n := nSn).
        - exact r.
        - assumption.  
        }
        destruct H as [n' [_ H]].
        exists n'.
        assumption.
    }
    intros t1 r1.
    destruct r as [_ r].
    specialize r with t1.
    apply r in r1.
    specialize IHT2 with (Ty_App t t1) (Ty_App t' t1).
    apply IHT2 in r1.
    + assumption.
    + unfold RED0.
      unfold RED0 in rd.
      destruct rd as [s rd].
      exists (s + 1).
      apply RED_app1.
      assumption. *)
Admitted.

(* R implies strongly normalizing *)
Lemma cr1 : forall {t : tm} {tp : tp},
    R t tp -> SN0 t.
Proof.
    (* intros ty K HR.
    induction K. unfold R in HR.
    - assumption.
    - unfold R in HR; fold R in HR.
      destruct HR as [sn0 _].
      assumption. *)
Admitted. 

Lemma cr3a : forall {t t1 : tm} {tp1 tp2 : tp } {m : nat},
  NEU t ->
  R t1 tp1 ->
  SN t1 m ->
  (forall t', RED0 t t' -> R t' (tpfun tp1 tp2)) ->
  R (tmapp t t1) tp2.
Proof.
  (* intros t t1 K1 K2 m neu r1 sn1 f.
  remember (Ty_App t t1) as tt.
  induction K2; unfold R; fold R.
  - admit.
  - split.
    + admit.
    + intros t0.  
  destruct rd.
  - (* Case REDapp1 *)
    subst.
    apply f in H.
    apply H.
    apply r1.
  - (* Case REDapp2 *)
    subst.
    inversion sn1 as [t1' m' Hsn1].
    specialize (Hsn1 t1' H).
    destruct Hsn1 as [n' [Hlt Hsn1']].
    apply cr3a with (tp1 := tp1) (tp2 := tp2) (neu := neu) (r1 := r1) (sn1 := Hsn1') (f := f).
  - (* Case REDapp3 *)
    subst.
    inversion neu; subst; contradiction. *)
Admitted.

(* How do we not need kinding here... If t is a value, it is neutral, 
  there are no t such that t --> t', so then we would have to prove R t K for all K?*)
Lemma cr3 : forall (t : tm) (tp : tp),
  NEU t ->
  (forall t', RED0 t t' -> R t' tp) ->
  R t tp.
Proof.
  (* intros t K neu H.
  induction K.
  - unfold R; fold R.
     admit.
      (* Suppose there is no t such that t to t', then by definition SN0 t*)
      (* So let t' such that RED0 t t'. Then R t' Kind_Base, so SN0 t'**)
        (* Then SN_backwards in some way. *)
  - unfold R; fold R; split.
    + admit. (* Same argument as above *)
    + intros t1 Rt1.
      remember (cr1 Rt1) as sn0.
      unfold SN0 in sn0.
      destruct sn0 as [sn_n sn].
      apply (cr3a neu Rt1 sn H). *)
Admitted. 

(* Proof in Barendreght: The Lambda Calculus, 2.1.17 *)
Lemma subst_preserves_reduction : forall t1 t2 t3 t2',
  subst1 t1 t2 t3 ->
  RED0 t2 t2' ->
  exists t3', RED0 t3 t3' /\ subst1 t1 t2' t3'.
Proof.
Admitted.


(* \. f  t --> subst t f t', where t' is the new term*)
Lemma lamSN : forall (t1 t2 t3: tm) (n : nat),
  subst1 t1 t2 t3 -> SN t3 n -> SN t2 n.
Proof.
(* We know that t3 normalizes in at most n steps
    Suppose t2 steps to t2', then by subst_preserves_reduction
    we know that t3 must also step, and then SN t3' (n - 1)
    
    then we do it again, but at some point we get subst1 t1 t2 t3 -> SN t3 0 -> SN t2 0
    Proof by contradiction: Again, we suppose t2 --> t2', but it cant, because then t3 must step somewhere, and it cant.
    So t2 cannot reduce, so it is a value, so SN t2 0. (since the implication condition is trivially true now)

*)
Admitted.

(* Ask Jacco: Classical reasoning? (law of excluded middle)*)
Lemma reduceFun :
  forall (f t : tm) (T1 T2 : tp),
    (R t T1 ->
     (forall (t1 t2 : tm),
        subst1 t1 f t2 -> R t1 T1 -> R t2 T2) ->
     R (tmapp (tmlam f) t) T2).
Proof.
  (* Insight: f should have only one free variable again*)
  intros f t T1 T2 RT1 RH.
  specialize (RH t).
  assert (exists t2, subst1 t f t2).
  {
    induction f.
    - induction n.
      + admit. (* t2 = t*)
      + admit. (* Should be impossible to create, so maybe we need a well-typedness for f with only one free var?*) 
        (* in this case, we cannot reduce though*)
        (* So it is a value? Well.... not according to our previous value definition. 
          a term like (\x. x y) (3) cannot reduce, but it is not a value....
          Very problematic: is it now still a superset of our deterministic STLC?
          *)
  }
  
  
  assert (exists n, SN f n) as SNf.
  - admit. (* idk *)
    (* idea: construct t2 such that subst1 t f t2*)
    (* Then we can use it in lamSN. we need that anyway I think for using it
       
       What if it doesnt exist?
       Then we cannot use REDAPP3.
       Now suppose we reduced the f and the t

       General proof idea: use backward_R (cr3) and show that all possible single step reductions work
       For betareduce it is given by hypotheses.
       For the others, we can go into induction, and since they are SN, we will at some point get to beta reduction
  *)
  
Admitted.

Lemma mainLemma :
  forall {G : tps}  {T : tp} { ts : tms } { t t' : tm } { n : nat  },
    DER G t T n ->
    RS0 ts G ->
    subst ts t t' ->
    R t' T.
Proof.
  intros G T ts t t' n der rs sub.
  generalize dependent ts.
  generalize dependent t'.
  induction der;
  intros t' ts rs sub.
  - (* Case DERvar *)
    inversion sub.
    apply (mainLemmaVar H H2).
    assumption.
  - (* Case DERlam *)
    inversion sub.
    unfold R; fold R.
    intros tm' Rtm'.
    subst...
    apply reduceFun with  (T1 := T1); [assumption|].
    intros t1 t2 sub1 r.
    specialize (IHder t2).
    pose proof (lemma20 H0 H2 sub1) as sub0.
    specialize (IHder (tmsmore ts t1)).
    destruct rs as [n rs_pred].
    pose proof (RSmore rs_pred r).
    pose proof (existT _ (S n) H) as rs.
    specialize (IHder rs sub0).
    assumption.

  - (* Case DERapp *)
  inversion sub.
  specialize (IHder1 t1' ts rs H2).
  specialize (IHder2 t2' ts rs H4).
  unfold R in IHder1; fold R in IHder1.
  specialize (IHder1 t2' IHder2).
  assumption.
Qed.

(* Definition of the `reduce` lemma *)
Lemma reduce : forall (t : tm) (T : tp),
  DER0 tpsnil t T -> R t T.
Proof.
  intros t T der.
  unfold DER0 in der.
  remember der as der'.
  clear Heqder'.
  destruct der as [s der].
  pose proof (existT _ 0 RSnil) as rs0.
  apply (mainLemma der rs0 (lemma10 der')).
Qed.