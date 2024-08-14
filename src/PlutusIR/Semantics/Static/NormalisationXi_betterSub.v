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

Definition closed_or_neutral (ts : tms) :=
let fix closed_or_neutral_helper (ts : tms) (i : nat) :=
  match ts with
  | tmsnil => True
  | tmsmore ts' t  => (closed t \/ neutral_var i t) /\ closed_or_neutral_helper ts' (i + 1)
  end
  in
  closed_or_neutral_helper ts 0.

Lemma subshi_scon : forall ts,
  closed_or_neutral ts -> subshi ts (scon ts).
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
  closed_or_neutral ts ->
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
    DER0 tpsnil tm T /\
    
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
Lemma lemma10 : forall {t : tm } { T : tp},
  subst tmsnil t t.
Proof with eauto.
  intros t tp.
  induction t.
  - apply SUBnil.
    unfold identity_sub.
    reflexivity.
  - apply SUBlam with (ts' := tmsnil).
    + apply SUBSHInil.
    + induction t. (* At some point t : Kind_Base, so induction on t will no longer give lamda case*)
      * apply SUBnil.
        admit. (* Yes. Easy *)
      * admit. (* a layer deeper, at some point we cannot go deeper! *)
      (* no clue. *) (* Hongwei Xi says it is possible. Induciton on T length?*)
      * inversion IHt.
        apply IHt1 in H3.
        apply IHt2 in H5.
        apply SUBapp; assumption.
  - apply SUBapp; assumption.
Admitted.

(* TODO: No clue *)
Lemma lemma20 :
  forall {ts ts': tms} {t t1 t' t'': tm} {G : tps} {T1 : tp} ,
    RS0 ts G ->
    subshi ts ts' -> 
    subst (tmsmore ts' (tmvar 0)) t t' ->
    R t1 T1 ->
    subst1 t1 t' t'' ->
    subst (tmsmore ts t1) t t''. (* I think this should be ts'*)
Proof.
  intros ts ts' t t1 t' t'' G T1.
  intros rs0 subshi sub Rt1 sub1.

  (* By closedness of R *)
  assert (ts' = ts) by admit.
  subst...
  clear subshi.
  generalize dependent t.
  generalize dependent t''.
  induction t'.
  (* t = t'*)
  - admit. (* straightforward*)
  - intros t'' sub1 t sub.
    apply IHt'.
  (* assert (exists t''', t'' = tmlam t''')   by admit. *)
  (* destruct H as [t''' H]. *)
  subst...
  apply SUBlam with (ts' :=  (tmsmore ts t1) ).
  + admit.
  + 


  (* Since verything that gets substituted does not interfere with each other, this should hold*)
  (* Suppose ts = t2

    Then we are actually asking: subst t2, and then t1 <=> subst t1 and then t2. Since t2 and t1 closed, yes.

  *)
  
  (* Idea: subshi ts ts' /\ RS0 ts G => ts = ts'*)
  (* t' has free var x. subst1 t1 t' t'' /\ R t1 T1 => no free x in t''*)
Admitted.



(* R is preserved by forward reduction *)
Lemma cr2 : forall {t t' : tm}  {tp : tp },
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

(* TODO: Ooo we need this in other places! *)
Lemma appSN1 : forall t1 t2 n,
  SN (tmapp t1 t2) n ->
  SN0 t1.
Proof.
  intros t1 t2 n sn.
  destruct sn as [fsn].
  apply backwardSN.
  intros t1' red.
  apply appSN1 with (t2 := t2) (n := n).
  apply fsn.
  apply REDapp1.
  exact red.
Admitted.

(* R implies strongly normalizing *)
Lemma cr1 : forall {t : tm} {tp : tp},
    R t tp -> SN0 t.
Proof.
    intros t tp HR.
    generalize dependent t.
    induction tp.
    
    - intros t Rt.
      destruct Rt as [_ Rt].
      assumption.
    - intros t Rt. 
    (* unfold R in Rt; fold R in Rt.
    destruct Rt as [_ Rt]. *)
    induction t.


    
    
      
      
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

(* Should follow by inverse logic of the above and confluence
    Possibly we don't even need the confluence *)
  (* I think we don't need confluence:
  Here (https://proofassistants.stackexchange.com/questions/4206/stlc-substitution-behaviour-with-lambda-body-normalisation?noredirect=1#comment8219_4206)
    I created a counter example for the deterministic semantics, but our statement is now
      about non-determenistic, and we only need to find one t3 that steps.
  Also in the above lemma Barendreght proved we don't need confluence, and this is just reverse? Makes sense to me*)

  (* In the forall case we do need confluence I think*)
Lemma subst_preserves_reduction' : forall {t1 t2 t2' t3' : tm} ,
  subst1 t1 t2' t3'
  ->
  RED0 t2 t2' -> 
  (exists t3 : tm, RED0 t3 t3' /\ subst1 t1 t2 t3). (* exists, or forall*)
Proof.
  intros t1 t2 t2' t3 T HsubR Hred2 t3' Hred3 Hsub.
  (* Use subst_preserves_reduction to find the intermediate term *)
   destruct (subst_preserves_reduction t1 t2 t3 t2' Hsub Hred2) 
    as [t3'' [Hred_t3_t3'' Hsub_t1_t2'_t3'']].
Admitted.

(* Lemma subst_helper : ,
  (forall t2, subst1 t f t2 -> R t2 T2) -> (RED0 f f') *)

(* TODO: similar lemma for t1 --> t1' *)

(* Now use this to get a fitting hypothesis for reduceFun!*)




(* TODO: NOT USED??? *)
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
Lemma reduceFun : forall {f t : tm} { T1 T2 : tp},
    SN0 f -> (* TODO: How do we get this SN f n?*)
    R t T1 ->
     (forall (t2 : tm),
        subst1 t f t2 -> R t2 T2) ->
     R (tmapp (tmlam f) t) T2.
Proof.
  (* Insight: f should have only one free variable again*)
  intros f t T1 T2 SN0f RT1 RH.
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
    intros f_n t_n n t SN_t f SN_f RH.
    assert (f_n = 0) by lia.
    assert (t_n = 0) by lia.
    apply cr3.
    + apply NEUapp.
    + intros t' red.
      inversion red.
      inversion H1.
      * admit. (* NOT POSSIBLE BY f_n = 0.*) 
      * admit.
      * specialize (RH t' H6).
        assumption.
  - intros f_n t_n n t SN_t f SN_f RH.
    apply cr3.
    + apply NEUapp.
    + intros t' red_ft.
      inversion red_ft as [red_ft_n red_ft'].
      inversion red_ft'.
      * assert (f_n' := t_n - 1). 
        inversion H3.
        assert (SN t'0 f_n') as SN_f' by admit. (* step preserves SN*)
        assert (k = f_n' + t_n) by admit. (* arithmetic stuff.*)
        specialize (IH f_n' t_n H8 t SN_t t'0 SN_f').
        assert (forall t2, subst1 t t'0 t2 -> R t2 T2).
        {
          intros t3 Hsub.
          destruct (@subst_preserves_reduction' _ f _ _ Hsub).
          - unfold RED0.
            exists s0.
            assumption.
          - destruct H9 as [H9_red H9_sub].
            specialize (RH x H9_sub).
            apply (cr2 RH H9_red).
        }
        specialize (IH H9).
        assumption.
      * admit. (* TODO: Analogous to above, implement once above sublemmas are verified*)
      * specialize (RH t' H3).
        assumption.  
Admitted.

(* doable I think with some: free in lemmas. *)
Lemma R_sub_removes_free_vars : forall t1 ts' t2 Ts' T0 T2,
  RS0 ts' Ts' -> DER0 (tpsmore Ts' T0) t1 T2 -> subst (tmsmore ts' (tmvar 0)) t1 t2 -> DER0  (tpsmore tpsnil T0) t2 T2.
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
      (* From RS0 (tmsmore tmsnil (tmvar 0)) G we know G has 1 element*)
      (* From TPI i T G we know that T in G at position i*)
      (* So i = 0 and G = T*)
      (* And then by RS0, we have R (tmvar i) T*)
      admit. 
    + subst...
      assert (tpslength G = tmslength ts) by admit. (* From RS0 ts G*)
      assert (tpslength G >= i + 1) by admit. (* From TPI i T G *)
      exfalso.
      lia.
    + apply (mainLemmaVar H H2).
      assumption.
    
  - (* Case DERlam *)
    inversion sub; subst...
    + admit. (* New SUBnil case: RS0 tmsnil G => len G = 0*)
      (* apply SUBlam with (ts := tmsmore tmsnil (tmvar 0)) in sub. *)
    (* contradiction in RS0 (tmsmore tmsnil (tmvar 0)) G ?, because tmvar 0 not closed*)
      unfold RS0 in rs.
      destruct rs as [rs_n rs].
      inversion rs.
      induction T; unfold R in H4; fold R in H4;
        destruct H4 as [H4_der _];
        inversion H4_der;
        inversion H4;
        inversion H7.
      
    + 
      unfold R; fold R.
      split.
      *  
        assert (ts = ts') by admit. (* by RS0 ts G, no free vars in ts, so no shifting*)
        subst...
        assert (DER0 (tpsmore tpsnil T1) t'0 T2).
        {
          apply R_sub_removes_free_vars with (t1 := t) (ts' := ts') (Ts' := G); try assumption.
          unfold DER0.
          exists s.
          assumption.
        }
        unfold DER0.
        unfold DER0 in H.
        destruct H as [H_DER_s H_DER].
        exists (S H_DER_s).
        apply DERlam.
        assumption.
      *  
      

      intros tm' Rtm'.
      subst...
      apply (@reduceFun _ _ T1 _); try assumption.
      -- assert (ts' = ts) by admit. (* by RS0 and subshi*)
        subst...
        
        
        assert (exists v, subst1 tm' t'0 v).
        {
          assert (DER0 (tpsmore tpsnil T1) t'0 T2).
          {
            apply R_sub_removes_free_vars with (t1 := t) (ts' := ts) (Ts' := G).
            - assumption.
            - unfold DER0.
              exists s.
              assumption.
            - assumption.  

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
        (* From SN (tmapp (tlam t'0) tm')
          we know that all reduction paths halt.
          One such reduction path is applying RED_lam to tmlam t'0.
          But we know that it halts, so we can only do this a finite amount of time,
          so t'0 must be halting.
        *)
        admit.
      
      --
      intros t2 sub1.
      specialize (IHder t2).
      pose proof (lemma20 rs H0 H2 Rtm' sub1) as sub0.
      specialize (IHder (tmsmore ts tm')).
      destruct rs as [n rs_pred].
      pose proof (RSmore rs_pred Rtm').
      pose proof (existT _ (S n) H) as rs.
      specialize (IHder rs sub0).
      assumption.
    

  - (* Case DERapp *)
  inversion sub; subst...
  + 
    
    assert (subst (tmsmore tmsnil (tmvar 0)) t1 t1) as sub_1 by apply SUBneutral.
    assert (subst (tmsmore tmsnil (tmvar 0)) t2 t2) as sub_2 by apply SUBneutral.

    specialize (IHder1 t1 (tmsmore tmsnil (tmvar 0)) rs sub_1).
    specialize (IHder2 t2 (tmsmore tmsnil (tmvar 0)) rs sub_2).
    unfold R in IHder1; fold R in IHder1.
    destruct IHder1 as [_ IHder1].
    specialize (IHder1 t2 IHder2).
    assumption.
  +   
  specialize (IHder1 t1' ts rs H2).
  specialize (IHder2 t2' ts rs H4).
  unfold R in IHder1; fold R in IHder1.
  destruct IHder1 as [IHder1_der IHder1].
  specialize (IHder1 t2' IHder2).
  assumption.
Admitted.

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
  apply (mainLemma der rs0 (@lemma10 t T)).
Qed.