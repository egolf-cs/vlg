Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From VLG Require Import ltac.
From VLG Require Import sigma.
From VLG Require Import matcher.
From VLG Require Import regexNotations.
From VLG Require Import simdef.
 
Theorem re_sim_correctF : forall e1 e2,
    re_sim e1 e2 = true -> re_sim_prop e1 e2.
Proof.
  intros.
  unfold re_sim in H.
  repeat dm; try(discriminate);
    repeat(first [rewrite Bool.orb_true_iff in *; destruct H
                 | rewrite Bool.andb_true_iff in *; destruct H]);
    try(discriminate);
    try(rewrite <- regex_eq_correct in *; discriminate);
    try(rewrite <- regex_eq_correct in *; subst; constructor);
    try(rewrite <- regex_eq_correct in *; rewrite H; constructor);
    try(rewrite <- regex_eq_correct in *; rewrite H0; constructor);
    try(rewrite <- regex_eq_correct in *; rewrite H; rewrite H0; constructor);
    try(rewrite <- regex_eq_correct in *; rewrite <- H; rewrite <- H0; constructor).
Qed.
  
Theorem re_sim_correctB : forall e1 e2,
    re_sim_prop e1 e2 -> re_sim e1 e2 = true.
Proof.
  intros.
  inv H; try(eapply re_sim_correctB_trans; eauto; reflexivity);
    unfold re_sim;
    try(rewrite Bool.orb_true_iff; left; rewrite <- regex_eq_correct; reflexivity);
    repeat dm; try(discriminate);
      repeat(first [rewrite Bool.orb_true_iff | rewrite Bool.andb_true_iff]);
      repeat(rewrite <- regex_eq_correct); repeat rewrite regex_eq_refl;
        try(right; right; right; right; right; split; reflexivity);
        try(right; left; right; right; right; split; reflexivity);
        try(left; right; right; right; right; split; reflexivity);
        try(left; left; right; right; right; split; reflexivity);
        try(right; right; right; right; left; split; reflexivity);
        try(right; left; right; right; left; split; reflexivity);
        try(left; right; right; right; left; split; reflexivity);
        try(left; left; right; right; left; split; reflexivity);
        try(right; right; right; left; right; split; reflexivity);
        try(right; left; right; left; right; split; reflexivity);
        try(left; right; right; left; right; split; reflexivity);
        try(left; left; right; left; right; split; reflexivity);
        try(right; right; right; left; left; split; reflexivity);
        try(right; left; right; left; left; split; reflexivity);
        try(left; right; right; left; left; split; reflexivity);
        try(left; left; right; left; left; split; reflexivity);
        try(right; right; left; right; right; split; reflexivity);
        try(right; left; left; right; right; split; reflexivity);
        try(left; right; left; right; right; split; reflexivity);
        try(left; left; left; right; right; split; reflexivity);
        try(right; right; left; right; left; split; reflexivity);
        try(right; left; left; right; left; split; reflexivity);
        try(left; right; left; right; left; split; reflexivity);
        try(left; left; left; right; left; split; reflexivity);
        try(right; right; left; left; right; split; reflexivity);
        try(right; left; left; left; right; split; reflexivity);
        try(left; right; left; left; right; split; reflexivity);
        try(left; left; left; left; right; split; reflexivity);
        try(right; right; left; left; left; split; reflexivity);
        try(right; left; left; left; left; split; reflexivity);
        try(left; right; left; left; left; split; reflexivity);
        try(left; left; left; left; left; split; reflexivity);
        try(right; left; left; left; right; split; reflexivity);
        try(right; right; right; right; split; reflexivity);
        try(right; right; right; left; split; reflexivity);
        try(right; right; left; right; split; reflexivity);
        try(right; right; left; left; split; reflexivity);
        try(right; left; right; right; split; reflexivity);
        try(right; left; right; left; split; reflexivity);
        try(right; left; left; right; split; reflexivity);
        try(right; left; left; left; split; reflexivity);
        try(left; right; right; right; split; reflexivity);
        try(left; right; right; left; split; reflexivity);
        try(left; right; left; right; split; reflexivity);
        try(left; right; left; left; split; reflexivity);
        try(left; left; right; right; split; reflexivity);
        try(left; left; right; left; split; reflexivity);
        try(left; left; left; right; split; reflexivity);
        try(left; left; left; left; split; reflexivity);
        try(right; right; right; split; reflexivity);
        try(right; right; left; split; reflexivity);
        try(right; left; right; split; auto; reflexivity);
        try(right; left; left; split; reflexivity);
        try(left; right; right; split; reflexivity);
        try(left; right; left; split; reflexivity);
        try(left; left; right; split; reflexivity);
        try(left; left; left; split; reflexivity);
        try(right; right; split; reflexivity);
        try(right; right; split; auto; reflexivity);
        try(right; left; split; auto; reflexivity);
        try(left; right; split; reflexivity);
        try(left; left; split; reflexivity);
        try(left; split; reflexivity);
        try(right; split; auto; reflexivity).
Qed.
