Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From VLG Require Import ltac.
From VLG Require Import sigma.
From VLG Require Import matcher.
From VLG Require Import regexNotations.
From VLG Require Import simdef.
From VLG Require Import simlemmas.                                             
        
Theorem re_sim_correct : forall e1 e2,
    re_sim e1 e2 = true <-> re_sim_prop e1 e2.
Proof.
  intros; split; [apply re_sim_correctF | apply re_sim_correctB].
Qed.


Lemma re_sim_refl : forall e, re_sim e e = true.
Proof.
  intros. rewrite re_sim_correct. constructor.
Qed.

Theorem re_sim_symm : forall e1 e2, re_sim e1 e2 = re_sim e2 e1.
Proof.
  intros. destruct (re_sim e1 e2) eqn:E; symmetry.
  - rewrite re_sim_correct in *. inv E; constructor.
  - rewrite false_not_true in *. intros C. destruct E.
    rewrite re_sim_correct in *. inv C; constructor.
Qed.
  
Theorem re_sim_equiv : forall e1 e2,
    re_sim e1 e2 = true -> re_equiv e1 e2.
Proof.
  intros. apply re_sim_correct in H.
  inv H;
    try(unfold re_equiv; intros; split; intros;
        inv H; auto; repeat(constructor); auto; reflexivity);
    unfold re_equiv; intros; split; intros.
  - inv H.
    + inv H2.
      * apply MUnionL. auto.
      * apply MUnionR. apply MUnionL. auto.
    + apply MUnionR. apply MUnionR. auto.
  - inv H.
    + apply MUnionL. apply MUnionL. auto.
    + inv H1.
      * apply MUnionL. apply MUnionR. auto.
      * apply MUnionR. auto.
  - inv H.
    + apply MUnionL. apply MUnionL. auto.
    + inv H1.
      * apply MUnionL. apply MUnionR. auto.
      * apply MUnionR. auto.
  - inv H.
    + inv H2.
      * apply MUnionL. auto.
      * apply MUnionR. apply MUnionL. auto.
    + apply MUnionR. apply MUnionR. auto.
  - inv H. inv H3. rewrite <- app_assoc. repeat(constructor); auto.
  - inv H. inv H4. rewrite app_assoc. repeat(constructor); auto.
  - inv H. inv H4. rewrite app_assoc. repeat(constructor); auto.
  - inv H. inv H3. rewrite <- app_assoc. repeat(constructor); auto.
Qed.

Lemma re_sim_nullable : forall e e',
    re_sim e e' = true
    -> nullable e = nullable e'.
Proof.
  intros. apply re_sim_equiv in H.
  unfold re_equiv in H. specialize (H []).
  do 2 rewrite <- nullable_bridge in H.
  apply Bool.eq_true_iff_eq. split; intros; symmetry; apply H; symmetry; auto.
Qed.
