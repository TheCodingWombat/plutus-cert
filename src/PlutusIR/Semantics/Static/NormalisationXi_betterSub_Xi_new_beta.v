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

(* CHANGES TO XI AND DONNELLY:
  - More relaxed substitution: beta reduction always allowed
  - Empty kinding in R
*)

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

Fixpoint tmslength (ts : tms) : nat :=
  match ts with
  | tmsnil => 0
  | tmsmore ts' _ => 1 + tmslength ts'
  end.

Fixpoint tpslength (tps : tps) : nat :=
  match tps with
  | tpsnil => 0
  | tpsmore tps' _ => 1 + tpslength tps'
  end.


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


Definition identity_sub (ts : tms) :=
  let fix identity_sub_helper (ts: tms) (i : nat) :=
    match ts with
    | tmsnil => True
    | tmsmore ts' (tmvar j) => (i = j) /\ identity_sub_helper ts' (i + 1)
    | _ => False
    end
    in
    identity_sub_helper ts 0.

Inductive subst : tms -> tm -> tm -> Prop :=
  | SUBnil : forall (ts : tms) (i : nat),
      identity_sub ts ->
      subst ts (tmvar i) (tmvar i)
  | SUBempty : forall (ts : tms) (i : nat), (* This rule also makes lemma10 not require derivation*)
      i + 1 > tmslength ts -> (* if i == 0, and length ts = 0, we should go into this case*)
      subst ts (tmvar i) (tmvar i)
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

Require Import Coq.Arith.PeanoNat.

Fixpoint closed_under (n : nat) (t : tm) : Prop :=
  match t with
  | tmvar x => x <= n
  | tmlam t1 => closed_under (S n) t1
  | tmapp t1 t2 => closed_under n t1 /\ closed_under n t2
  end.

Definition closed (t : tm) : Prop :=
  closed_under 0 t.

Definition neutral_var i t : Prop :=
  match t with
  | tmvar j => i = j
  | _ => False
  end.

(* shift closed or neutral *)
Definition scon_tm (t : tm) : tm :=
match t with
      | tmvar i => tmvar (i + 1)
      | t' => t' (* Closed term, no shifting required. TODO: Make this funciton only callable about closed terms *)
end.

Fixpoint scon (ts : tms) : tms :=
  match ts with
  | tmsnil => tmsnil
  | tmsmore ts' t => tmsmore (scon ts') (scon_tm t)
  end.

Definition closed_or_neutral_tms (ts : tms) :=
let fix closed_or_neutral_helper (ts : tms) (i : nat) :=
  match ts with
  | tmsnil => True
  | tmsmore ts' t  => (closed t \/ neutral_var i t) /\ closed_or_neutral_helper ts' (i + 1)
  end
  in
  closed_or_neutral_helper ts 0.

Fixpoint closed_tms (ts : tms) :=
  match ts with
  | tmsnil => True
  | tmsmore ts' t => closed t /\ closed_tms ts'
  end.

Lemma subshi_scon : forall ts,
  closed_or_neutral_tms ts -> subshi ts (scon ts).
Proof.
  intros ts corn.
  remember (tmslength ts) as n.
  generalize dependent ts.
  induction n.
  - intros ts corn emptyts.
    unfold tmslength in emptyts.
    simpl in emptyts.
    destruct ts.
    + simpl.
      apply SUBSHInil.
    + simpl in emptyts.
      discriminate. 
  - intros ts corn snlength.   
    destruct ts.
    + apply SUBSHInil.
    + apply SUBSHImore.
      * fold scon.
        shelve. (* Follows almost directly from IHn*)
      * (* clue is that t is closed or neutral *)
        destruct t.
        -- simpl scon_tm.
           apply TMSHIvargte.
           lia.
        -- (* here we know that tm lam is closed or neutral, it is not neutral, so it is closed*)
          assert (closed (tmlam t)) by shelve.
          simpl scon_tm.
          (* Lemma that shifts neutral terms is identity TODO*)
Admitted.

Fixpoint get_tmi (tms : tms) (i : nat) : option tm := 
  match tms with
  | tmsnil => None
  | tmsmore ts' t => if Nat.eqb i 0 then Some t
      else get_tmi ts' (i - 1)
  end.

Lemma get_tmi_sound : forall tms i t,
  get_tmi tms i = Some t -> TMI i t tms.
Proof.
Admitted.

Lemma get_tmi_Some : forall i tms t,
  i + 1 <= tmslength tms -> get_tmi tms i = Some t -> TMI i t tms.
Proof.
Admitted.

Lemma get_tmi_None_inversion : forall (ts : tms) (i : nat),
  get_tmi ts i = None -> ts = tmsnil.
Proof.
Admitted.

(* TODO: Should work without closed/neutral assumption*)
Lemma subst_exists : forall ts t2 T2 G,
  closed_or_neutral_tms ts ->
  DER0 G t2 T2 -> exists t3, subst ts t2 t3.
Proof.
  (* Proof strategy: induction on derivation length of t2, so that we know a lot about the body of a lambda*)
  intros ts t2 T2 G cOrN der0.
  unfold DER0 in der0.
  destruct der0 as [s der0].
  generalize dependent t2.
  generalize dependent ts.
  generalize dependent T2.
  generalize dependent G.
  induction s as [s IH] using (well_founded_induction lt_wf).

   induction t2.
    - intros der. (* impossible to need steps to get to a derivation of var*)
      inversion der.
      
    subst...
    destruct (Nat.ltb (tmslength ts) (n + 1)) eqn:Hlen.
    + apply Nat.ltb_lt in Hlen.
      exists (tmvar n).
      apply SUBempty.
      assumption.
    + apply Nat.ltb_ge in Hlen.
      destruct (get_tmi ts n) as [t |] eqn:Hget.
      * exists t.
        apply get_tmi_sound in Hget.
        apply SUBvar.
        assumption.

      * apply get_tmi_None_inversion in Hget.
        subst...  
        simpl in Hlen.
        lia.
    - intros der.   
      assert (exists t3', subst ts (tmlam t2) (tmlam t3')).
      {
        
        assert (exists t3', subst (tmsmore (scon ts) (tmvar 0)) t2 t3').
        {
          inversion der.
          assert (closed_or_neutral (tmsmore (scon ts) (tmvar 0))) as cOrN' by admit. (* variables that get shifted one position in ts are also shifted in value, so they remain neutral*)
          assert (s0 < s) as s0_smaller by lia.
          specialize (IH s0 s0_smaller (tpsmore G T1) T0 (tmsmore (scon ts) (tmvar 0)) cOrN' t2 H1).
          assumption.
        }
        destruct H as [H0_t3' H0].
        exists (H0_t3').
        apply SUBlam with (ts' := scon ts).
        - apply subshi_scon.
          assumption.
        - assumption.  
                 
      }
      destruct H as [t3' H].
      exists (tmlam t3').
      assumption.

    - intros der.
      inversion der as [| |a1 T1 a3 a4 a5 s1 s2 der_t2_1 der_t2_2].
      assert (s1 < s) as s1_smaller by lia.
      assert (s2 < s) as s2_smaller by lia.
      
      subst...
      remember IH as IH'.
      clear HeqIH'.
      specialize (IH s1 s1_smaller G (tpfun T1 T2) ts cOrN t2_1 der_t2_1).
      specialize (IH' s2 s2_smaller G T1 ts cOrN t2_2 der_t2_2).
      destruct IH as [t3_1 IHs].
      destruct IH' as [t3_2 IHs'].
      exists (tmapp t3_1 t3_2).
      apply SUBapp.
      * assumption.
      * assumption.
Admitted. 




Inductive SubstBeta : tm -> tm -> tm -> tm -> tm -> Prop :=
  | SubstBetaIntro : forall t1 t1' t2 t3 t3',
    tmshi t1 t1' 0 -> 
    tmshi t3 t3' 0 -> 
    subst (tmsmore tmsnil t1') t2 t3' -> 
    SubstBeta t1 t1' t2 t3 t3'.

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

  | REDapp3 : forall (t v vshi t' t'shi : tm),
  (* Fixed this definition, since it was meant for beta reduction*)
      SubstBeta v vshi t t' t'shi ->
      RED (tmapp (tmlam t) v) t' 0.

Definition RED0 (t t' : tm) : Prop :=
  exists s, RED t t' s.

(* Boring proof, but good to be sure.*)
Lemma testBetaReductAll : forall t,
  RED (tmapp (tmlam (tmapp (tmvar 0) (tmvar 1))) (tmvar 3)) t 0 -> t = (tmapp (tmvar 3) (tmvar 0)).
Proof.
  intros t Hred.
  inversion Hred.
  inversion H2.
  subst...
  inversion H3; try lia.
  simpl in H1.
  subst...
  inversion H5.
  subst...
  inversion H7; subst...
  { inversion H6; lia. }
  { simpl in H6. lia. }
  inversion H6; try lia; subst...
  inversion H9; subst; [inversion H8| |inversion H8; inversion H13]; try lia.
  inversion H4.
  subst...
  inversion H11; try lia.
  clear H5 H2 H4.
  assert (i = 4 - 1). (* Why doesnt lia do this...*)
  {
    rewrite <- H.
    lia.
  }
  simpl in H2.
  subst...
  inversion H13; try lia.
  assert (i= 1 - 1).
  {
    rewrite <- H1.
    lia.
  }
  simpl in H12.
  subst...
  reflexivity.
Qed.

(* Validated for t = (0 1) ts = 1, t1 = arbitrary*)
Lemma lemma20 :
  forall {ts ts': tms} {t t1 t' t'' t1_shi t''_shi: tm} ,
    subshi ts ts' -> 
    subst (tmsmore ts' (tmvar 0)) t t' ->
    SubstBeta t1 t1_shi  t' t'' t''_shi ->
    subst (tmsmore ts t1) t t''. 
Proof.
Admitted.

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

Definition RS0_closed (ts : tms) (G : tps) : Type :=
  {n : nat & RS ts G n & closed_tms ts}.

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
    simpl in H0.
    
    
    (* t is the S i - 1 = ith term in ts0, and T is the ith term in G, and RS ts0 G, so easy.*)
Admitted.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Wf_nat.

(* NOTE: We use inversion der instead of induction der because with induction 
  the var case is not seen as impossible...
  CONSEQUENCE: Now we need this s in the derivation, but we may also be able to use structural induction on der?
  *)
(* NOTE: well-kindedness removed, shoult now be possible with new subst*)
Lemma lemma10 : forall {t : tm } {ts : tms} { T : tp} {G : tps},
  DER0 G t T -> identity_sub ts -> subst ts t t.
Proof with eauto.
(* TODO: Induction on kinding length! Different idea: Cant we do induction on T instead of on the derivation? *)
  intros t tms tp G der idsub.
  unfold DER0 in der.
  destruct der as [s der].
  generalize dependent G.
  generalize dependent tp.
  generalize dependent tms.
  generalize dependent t.
  induction s; intros t tms idsub tp G der.
  - inversion der. apply SUBnil. assumption.
  - induction t.
  + apply SUBnil.
    assumption.
  + apply SUBlam with (ts' := tms). (* not true, tms should be shifted one to obtain tms', then tms'::tmvar 0 is still identity_sub *)
    * admit. (* not true! see above *)
    * inversion der. (* Now we can use IHs! (if we have the correct tms')*)
      admit.
  + apply SUBapp; assumption.
Admitted.

Lemma cr1 : forall t tp,
  R t tp -> SN0 t.
Proof.
Admitted.


(* R is preserved by forward reduction *)
Lemma cr2 : forall {t t' : tm}  {tp : tp },
  R t tp -> RED0 t t' -> R t' tp.
Proof.
Admitted.
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


(* TODO: Ooo we need this in other places! *)
Lemma appSN1 : forall t1 t2 n,
  SN (tmapp t1 t2) n ->
  SN0 t1.
Proof.
  
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

(* Inverse of proof in Barendreght: The Lambda Calculus, 2.1.17? *)
Lemma subst_helper : forall {t1 t2' t3' t2} ,
  subst t1 t2' t3' ->
  RED0 t2 t2' ->
  exists t3, (subst t1 t2 t3 /\ RED0 t3 t3').
Proof.
Admitted.

(* makes sense? *)
Lemma shift_helper2 : forall t1 t2 t3 t1' t2' t3', 
  tmshi t1 t1' 0 ->
  tmshi t2 t2' 1 ->
  tmshi t3 t3' 0 ->
  subst (tmsmore tmsnil t1') t2' t3' ->
  subst (tmsmore tmsnil t1) t2 t3.
Proof.
  (* tmshi t2 t2' 1, so 0 remains 0. So in t2', 0 gets replaced by t1', 
      and in t2, 0 gets replaced by t1
    it should just be true ok.
  *)
Admitted.

(* So much machinery, aaa
*)
Lemma shift_unique : forall { t1 t2 t3 l} ,
  tmshi t1 t3 l ->
  tmshi t2 t3 l ->
  t1 = t2.
Proof.
Admitted.

Lemma shift_helper : forall t1 t2 t1_shi t2_shi l, 
  tmshi t1 t1_shi l -> 
  tmshi t2 t2_shi l ->
  RED0 t1_shi t2_shi ->
  RED0 t1 t2.
Proof.
  intros t1 t2 t1_shi t2_shi l tmshit1 tmshit2 redt1shi.
  unfold RED0.
  unfold RED0 in redt1shi.
  destruct redt1shi as [s redt1shi].
  exists s.
  generalize dependent l.
  generalize dependent t1.
  generalize dependent t2.
  generalize dependent t1_shi.
  generalize dependent t2_shi.
  induction s; intros t2_shi t1_shi redt1shi t2 t1 l tmshit1 tmshit2.
  - (* Since I generalized this to l this doesnt work anymore. But it does work for
      tmshi t1 t1_shi 0... We need a sort of alpha equivalence I think.*)
    inversion redt1shi.
    subst...
    
    inversion tmshit1; subst...
    inversion H3; subst...
    apply REDapp3 with (vshi := v) (t'shi := t2_shi).
    subst...
    apply SubstBetaIntro.
    + assumption. admit.
    + assumption. admit.
    + inversion H3.
      subst...
      destruct H.
      apply shift_helper2 with (t1':= t1') (t2' := t0) (t3' := t3'); try assumption.
      admit.
    + admit. + admit. 
  - inversion redt1shi; subst...
    + inversion tmshit2; subst...
      inversion tmshit2; subst...
      inversion tmshit1; subst...
      inversion tmshit1; subst...
      apply REDlam.
      specialize (IHs t' t H2 t0 t2 (S l) H4 H1).
      assumption.
    + inversion tmshit2; subst...
      inversion tmshit1; subst...
      specialize (IHs t1' t0 H2 t4 t2 l H4 H3).
      pose proof (shift_unique H5 H7).
      subst...
      apply REDapp1.
      assumption.
    + (* analogous*)
Admitted.

Lemma beta_reduction_helper : forall {t1 t1_shi t2' t3' t3_shi' t2} ,
  SubstBeta t1 t1_shi t2' t3' t3_shi' ->
  RED0 t2 t2' ->
  exists t3 t3_shi, (SubstBeta t1 t1_shi t2 t3 t3_shi /\ (RED0 t3 t3' \/ t3 = t3')).
Proof.
  intros t1 t1_shi t2' t3' t3_shi' t2 subBetat2' redt2.
  apply REDapp3 in subBetat2'.
    


(* Is this even true? Don't we need a confluent argument?*)
(* Not smart enough to do the induction ;)*)
(* This fact is programmed right into the HOAS reduction definition it seems
    there if tmlam t2 --> tmlam t2' iff forall t1, SubstBeta t1 _ t2 --> SubstBeta t1 _ t2'*)
Lemma beta_reduction_helper : forall {t1 t1_shi t2' t3' t3_shi' t2} ,
  SubstBeta t1 t1_shi t2' t3' t3_shi' ->
  RED0 t2 t2' ->
  exists t3 t3_shi, (SubstBeta t1 t1_shi t2 t3 t3_shi /\ (RED0 t3 t3' \/ t3 = t3')).
Proof.
  intros t1 t1_shi t2' t3' t3_shi' t2 substbeta red.
  apply REDapp3 in substbeta as prrr.
  assert (RED0 (tmapp (tmlam t2) t1) t3') by admit.
  inversion H. (* How to continue frmo here? *)
    
  inversion substbeta.
  subst...
  pose proof (subst_helper H1 red) as existsT3.
  destruct existsT3 as [t3_shi_found [t3sub t3red]].
  assert (exists t3, tmshi t3 t3_shi_found 0) as [t3_found tmshi_t3] by admit.
    (* Only true if t3_shi_found does not contain 0
        Proof:
          by t3sub : subst (tmsmore tmsnil t1_shi) t2 t3_shi_found
          we know 0 in t2 is replaced by t1_shi to obtain t3_shi
          So if t1_shi does not contain 0, then done.
          But tmshi t1 t1_shi, so all 0 in t1 becomes 1 in t1_shi.
      *)
  exists t3_found.
  exists t3_shi_found.
  split.
  - apply SubstBetaIntro; assumption.
  (* - apply shift_helper. *) - admit.
Admitted.


(* TODO: NOT USED??? *)
(* \. f  t --> subst t f t', where t' is the new term*)
Lemma lamSN : forall (t f t2 t_shi t2_shi : tm) (n : nat),
    SubstBeta t t_shi f t2 t2_shi -> SN t2 n -> SN f n.
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
Lemma reduceFun : forall {f t : tm} { T1 T2 : tp},
    
    R t T1 ->
     (forall (t_shi t2 t2_shi : tm),
        SubstBeta t t_shi f t2 t2_shi -> R t2 T2) ->
     R (tmapp (tmlam f) t) T2.
Proof.
  intros f t T1 T2 RT1 RH.
  assert (SN0 f) as SN0f by admit. (* No clue, how to get this t2? Basically we have to show existence of t2 s.t. SubstBeta t t_shi f t2 t2_shi*)
  destruct SN0f as [f_n SNf].
  apply cr1 in RT1.
  unfold SN0 in RT1.
  destruct RT1 as [t_n RT1].
  remember (f_n + t_n) as n eqn:Hn.
  generalize dependent f .
  generalize dependent t.
  generalize dependent t_n.
  generalize dependent f_n.
  induction n as [|k IH].
  - (* f_n = t_n = 0, so only reduction possible is beta reduction *) 
    intros f_n t_n n t SN_t f RH SN_f.
    assert (f_n = 0) by lia.
    assert (t_n = 0) by lia.
    apply cr3.
    + apply NEUapp.
    + intros t' red.
      inversion red.
      inversion H1.
      * admit. (* NOT POSSIBLE BY f_n = 0.*) 
      * admit. (* idem t_n *)
      * specialize (RH vshi t' t'shi H6).
        assumption.
  - intros f_n t_n n t SN_t f RH SN_f.
    apply cr3.
    + apply NEUapp.
    + intros t' red_ft.
      inversion red_ft as [red_ft_n red_ft'].
      inversion red_ft'.
      * assert (f_n' := t_n - 1). 
        inversion H3.
        rename t'0 into f'.
        assert (SN f' f_n') as SN_f' by admit. (* step preserves SN*)
        assert (k = f_n' + t_n) by admit. (* arithmetic stuff.*)
        specialize (IH f_n' t_n H8 t SN_t f').
        (* assert (forall t_shi t2 t2_shi, SubstBeta t t_shi t'0 t2 t2_shi -> R t2 T2) as RH'.
        { (* Maybe with new SubstBeta definition we don't need subst_preserves_reduciton' (maybe it is not even true!)*)
          intros t_shi t3 t2_shi subt'0.
          assert (RED0 f t'0) as redf_t'0 by admit.
          pose proof (beta_reduction_helper subt'0 redf_t'0) as substf.
          destruct substf as [t2f [t2f_shi [substf redt2]]].
          specialize (RH t_shi t2f t2f_shi substf).
          
          pose proof (cr2 RH redt2).
          assumption.

        } *)
        specialize (IH RH' SN_f').
        assumption.
        admit. 
      *  admit. (* TODO: Analogous to above, implement once above sublemmas are verified*)
      * specialize (RH vshi t' t'shi H3).
        assumption.  
Admitted.

(* doable I think with some: free in lemmas. *)
(* assumes closedness? *)
Lemma R_sub_removes_free_vars : forall t1 ts' t2 Ts' T0 T2,
  closed_tms ts' -> RS0 ts' Ts' -> DER0 (tpsmore Ts' T0) t1 T2 -> subst (tmsmore ts' (tmvar 0)) t1 t2 -> DER0  (tpsmore tpsnil T0) t2 T2.
Proof.
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
    + subst...
      (* By cr4 as below, but also by:
          length ts is length G. pos i in G, so pos i in ts.
          ts identity_subst, so pos i in ts is (var i)
          then by RS0 ts G we have R (var i) T (also by TPI i T G)
      *)
      admit. (* By cr4 I think! Since var i is normal and neutral*) 

    + subst...
      assert (tpslength G = tmslength ts) by admit. (* From RS0 ts G*)
      assert (tpslength G >= i + 1) by admit. (* From TPI i T G *)
      exfalso.
      lia.
    + apply (mainLemmaVar H H2).
      assumption.
      
    
  - (* Case DERlam *)
    inversion sub; subst...
     
      unfold R; fold R.
      
      

      intros tm' Rtm'.
      subst...
      apply (@reduceFun _ _ T1 _); try assumption.
      
      
         (* Body strongly normalising, kind of works*)
        (* subst...
        
        
        assert (exists v, subst1 tm' t'0 v).
        {
          assert (DER0 (tpsmore tpsnil T1) t'0 T2).
          {
            apply R_sub_removes_free_vars with (t1 := t) (ts' := ts) (Ts' := G).
            - assumption.
            - unfold DER0.
              exists s.
              assumption.
            - admit. (* I think this is fixed by: RS0 ts => RS0 ts' where subshi ts ts'*)

          }
          apply subst_exists with (T2 := T2) (G := tpsmore tpsnil T1).
          + admit. (* By R tm' T1, tm' closed*) 
          + assumption.  
          
        }
        destruct H as [v Hsub1].
        pose proof (lemma20 rs H0 H2 Rtm' Hsub1) as sub0.
        specialize (IHder v (tmsmore ts tm')).
        destruct rs as [ n rs_pred ].
        pose proof (RSmore rs_pred Rtm').
        pose proof (existT _ (S n) H) as rs.
        specialize (IHder rs sub0).
        apply cr1 in IHder.
        assert (SN0 (tmapp (tmlam t'0) tm')).
        {
          apply backwardSN.
          exists v.
          split.
          - unfold RED0.
            exists 0.
            apply REDapp3.
            assumption.
          - assumption. 
        }
        destruct H1 as [H0_n H1].
        apply appSN1 in H1.
        (* From SN (tmapp (tlam t'0) tm')
          we know that all reduction paths halt.
          One such reduction path is applying RED_lam to tmlam t'0.
          But we know that it halts, so we can only do this a finite amount of time,
          so t'0 must be halting.
        *)
        admit. *)
      
       
      intros t_shi t2 t'0' t2_shi sub1.
      specialize (IHder t2).
      pose proof (lemma20 H0 H2 sub1) as sub0.
      specialize (IHder (tmsmore ts tm')).
      destruct rs as [n rs_pred].
      pose proof (RSmore rs_pred Rtm').
      pose proof (existT _ (S n) H) as rs.
      specialize (IHder rs sub0).
      assumption.
    

  - (* Case DERapp *)
  inversion sub; subst...
  
    
  specialize (IHder1 t1' ts rs H2).
  specialize (IHder2 t2' ts rs H4).
  destruct rs as [rs_n rs].
  unfold R in IHder1; fold R in IHder1.
  
  specialize (IHder1 t2' IHder2).
  assumption.
Admitted.

(* Definition of the `reduce` lemma *)
Lemma reduce : forall (t : tm) (T : tp),
  DER0 tpsnil t T -> R t T.
Proof.
  intros t T der.
  remember der as der'.
  unfold DER0 in der.
  
  clear Heqder'.
  destruct der as [s der].
  pose proof (existT _ 0 RSnil) as rs0.
  assert (identity_sub tmsnil) as tmsnil_identity.
  {
    unfold identity_sub.
    reflexivity.
  }
  apply (mainLemma der rs0 (@lemma10 t tmsnil T tpsnil der' tmsnil_identity)).
Qed.