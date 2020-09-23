Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.
Require Import Ascii.

Ltac inv H := inversion H; subst; clear H.

Variable Sigma : Type.
Variable Sigma_dec : forall(a a' : Sigma), {a = a'} + {a <> a'}.
Theorem Sigma_dec_refl : forall(T : Type) (p1 p2 : T) (a : Sigma), p1 = if Sigma_dec a a then p1 else p2.
  intros T p1 p2 a.
  destruct (Sigma_dec a a).
  - reflexivity.
  - contradiction.
Qed.
Definition String : Type := list Sigma.

(* Didn't bother with Intersection and Complement yet *)
Inductive regex : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : Sigma)
  | App (r1 r2 : regex)
  | Union (r1 r2 : regex)
  | Star (r : regex).

Inductive exp_match : String -> regex -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
      exp_match (s1 ++ s2) (Star re).

(*
Inductive exp_match : String -> regex -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
                          
  (* Had to restrict this case with H0 to avoid infinite regress.
   Both s1 and s2 must "contribute" to s1 ++ s2.
   The set of possible s1 ++ s2 without H0 is equivalent to the set with H0,
   except for the empty string, which is addressed with MStar0. *)
  | MStarApp s1 s2 re
                 (H0 : s1 <> [])
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
      exp_match (s1 ++ s2) (Star re).*)

Fixpoint nullable (r : regex) : bool:=
  match r with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => false
  | App r1 r2 => andb (nullable r1) (nullable r2)
  | Union r1 r2 => orb (nullable r1) (nullable r2)
  | Star _ => true
  end.

Fixpoint nullify (r : regex) := if (nullable r) then EmptyStr else EmptySet.

Fixpoint derivative (a : Sigma) (r : regex) :=
  match r with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char x => if Sigma_dec x a then EmptyStr else EmptySet
  | App r1 r2 => if (nullable r1) then Union (App (derivative a r1) r2) (derivative a r2)
                                  else (App (derivative a r1) r2)               
  | Union r1 r2 => Union (derivative a r1) (derivative a r2)
  | Star r => App (derivative a r) (Star r)
  end.

Fixpoint exp_matchb (s : String) (r : regex) :=
  match s, r with
  | [], _ => nullable r
  | x::xs, _ => exp_matchb xs (derivative x r)
  end.

Lemma nil_right : forall(s : String), s ++ [] = s.
Proof.
  induction s.
  - simpl. reflexivity.
  - simpl. rewrite IHs. reflexivity.
Qed.

Lemma nil_left : forall(s : String), [] ++ s = s.
Proof.
  intros s. simpl. reflexivity.
Qed.

Lemma empty_app : forall(s1 s2 : String), s1 ++ s2 = [] -> s1 = [] /\ s2 = [].
Proof.
  intros s1 s2 H. destruct s1; destruct s2; try(simpl in H; discriminate).
  - split; reflexivity.
Qed.

Theorem nullable_bridge : forall(r : regex),
    true = nullable r <-> exp_match [] r.
Proof.
  intros r. split; intros H.
  - induction r; try(simpl in H; discriminate).
    + apply MEmpty.
    + simpl in H. destruct (nullable r1); destruct (nullable r2); try(simpl in H; discriminate).
      rewrite <- nil_left with (s := []). apply MApp.
      * apply IHr1. reflexivity.
      * apply IHr2. reflexivity.
    + simpl in H.  destruct (nullable r1); destruct (nullable r2).
      * apply MUnionL. apply IHr1. reflexivity.
      * apply MUnionL. apply IHr1. reflexivity.
      * apply MUnionR. apply IHr2. reflexivity.
      * simpl in H. discriminate.
    + apply MStar0.
  - induction r.
    + inversion H.
    + simpl. reflexivity.
    + inversion H.
    + simpl. inversion H. apply empty_app in H1. destruct H1.
      rewrite H1 in H3. rewrite H5 in H4.
      apply IHr1 in H3. apply IHr2 in H4.
      rewrite <- H3. rewrite <- H4. simpl. reflexivity.
    + simpl. inversion H.
      * apply IHr1 in H2. rewrite <- H2. destruct (nullable r2); simpl; reflexivity.
      * apply IHr2 in H1. rewrite <- H1. destruct (nullable r1); simpl; reflexivity.
    + simpl. reflexivity.
Qed.

(* star_concat upto concat_star necessary for hard star case of der_match *)
Lemma star_concat :
  forall s r',
    exp_match s (Star r')
    -> (exists xss : list (list Sigma),
          s = concat xss
          /\ (forall xs,
                In xs xss
                -> exp_match xs r')).
Proof.
  intros s r' hm.
  remember (Star r') as r. generalize dependent r'. 
  induction hm; intros r' heq; inv heq.
  - exists []; split; auto.
    intros xs hi; inv hi.
  - destruct (IHhm2 r') as (xss' & heq & hall); subst; auto.
    exists (s1 :: xss'); split; auto.
    intros xs hi.
    destruct hi as [hh| ht]; subst; auto.
Qed.

Definition rm_empty (yss : list String) :=
  filter (fun l => match l with | [] => false | _ => true end) yss.

Lemma rm_empty_mute : forall(yss : list String),
    concat (rm_empty yss) = concat yss.
Proof.
  intros yss. induction yss.
  - simpl. reflexivity.
  - simpl. destruct a.
    + simpl. apply IHyss.
    + simpl. rewrite IHyss. reflexivity.
Qed.

Lemma rm_empty_no_empty : forall(ys : String) (yss : list String),
    In ys (rm_empty yss) -> ys <> [].
Proof.
  intros ys yss H. unfold not. intros C. rewrite C in H.
  unfold rm_empty in H. induction yss.
  - simpl in H. contradiction.
  - simpl in H. destruct a.
    + apply IHyss in H. contradiction.
    + simpl in H. destruct H.
      * discriminate.
      * apply IHyss in H. contradiction.
Qed.

Lemma filtered_subset : forall(xs : String) (yss : list String),
    In xs (rm_empty yss) -> In xs yss.
Proof.
  intros xs yss. generalize dependent xs. induction yss; intros xs H.
  - simpl in H. contradiction.
  - simpl. destruct a.
    + simpl in H. right. apply IHyss. apply H.
    + simpl in H. destruct H.
      * left. apply H.
      * right. apply IHyss. apply H.
Qed.

Lemma star_concat_no_empt : forall(s : String) (r' : regex),
    s <> []
    -> exp_match s (Star r')
    -> (exists xss : list (list Sigma),
          s = concat xss
          /\ (forall xs,
                In xs xss
                -> exp_match xs r' /\ xs <> [])).
Proof.
  intros s r' Hempty Hstar. apply star_concat in Hstar.
  destruct Hstar as (yss & heq & hall).
  exists(rm_empty yss). split.
  - rewrite rm_empty_mute. apply heq.
  - intros xs H. split.
    + apply hall.  apply filtered_subset in H. apply H.
    + apply rm_empty_no_empty in H. apply H.
Qed.

Lemma concat_star : forall(xss : list String) (r : regex),
    (forall xs : list Sigma, In xs xss -> exp_match xs r) -> exp_match (concat xss) (Star r).
Proof.
  intros xss r H. induction xss.
  - simpl. apply MStar0.
  - replace (concat (a :: xss)) with (a ++ (concat xss)).
    + apply MStarApp.
      * apply H. simpl. left. reflexivity.
      * apply IHxss. intros xs H1. apply H. simpl. right. apply H1.
    + simpl. reflexivity.
Qed.
                     
Theorem der_matchb : forall(a : Sigma) (s : String) (r : regex),
    true = exp_matchb (a::s) r <-> true = exp_matchb s (derivative a r).
Proof.
  intros a s r.
  split; generalize dependent r; induction s; intros r H; simpl; simpl in H; apply H.
Qed.

Theorem der_match : forall(a : Sigma) (s : String) (r : regex),
    exp_match (a::s) r <-> exp_match s (derivative a r).
Proof.
  intros a s r.
  split.
  {
    generalize dependent s. induction r; intros s H.
    - inv H.
    - inv H.
    - destruct s.
      + destruct (Sigma_dec t a).
        * rewrite e. simpl. rewrite <- Sigma_dec_refl. apply MEmpty.
        * inv H. contradiction.
      + inv H.
    - simpl. destruct(nullable r1) eqn:E.
      + inv H. destruct s1.
        * apply MUnionR. apply IHr2. rewrite <- H1. simpl. apply H4.
        * apply MUnionL. simpl in H1. injection H1. intros Happ Hchar.
          rewrite <- Happ. rewrite Hchar in H3. apply IHr1 in H3.
          apply MApp.
          -- apply H3.
          -- apply H4.
      + inv H. destruct s1.
        * apply nullable_bridge in H3. rewrite E in H3. discriminate.
        * simpl in H1. injection H1. intros Happ Hchar.
          rewrite <- Happ. rewrite Hchar in H3. apply IHr1 in H3.
          apply MApp.
          -- apply H3.
          -- apply H4.
    - simpl. inv H.
      + apply IHr1 in H2. apply MUnionL. apply H2.
      + apply IHr2 in H1. apply MUnionR. apply H1.
      (* hard_star: This case was the hard one *)
    - apply star_concat_no_empt in H. destruct H as (xss & heq & hall).
      + assert (H : exists(s1 : String) (yss : list String),
                   ((a :: s1) :: yss) = xss).
        {
          destruct xss.
          - simpl in heq. discriminate.
          - simpl in heq. destruct l eqn:E.
            + apply hall in E.
              * contradiction.
              * rewrite E. simpl. left. reflexivity.
            + exists(l0). exists(xss). simpl in heq.
              injection heq. intros I1 I2. rewrite I2. reflexivity.
        }
        destruct H as [s1]. destruct H as [yss].
        rewrite <- H in hall.
        assert (A : In (a :: s1) ((a :: s1) :: yss)).
        { simpl. left. reflexivity. } 
        simpl. replace s with (s1 ++ (concat yss)).
        * apply MApp.
          -- apply IHr. apply hall in A. destruct A. apply H0.
          -- rewrite H in hall.
             assert (A1 : forall xs : list Sigma, In xs xss -> exp_match xs r).
             { intros xs. intros HA1. apply hall in HA1. destruct HA1. apply H0. }
             apply concat_star. intros xs H1. apply A1.
             rewrite <- H. simpl. right. apply H1.
        * assert (A1 : concat ((a :: s1) :: yss) = concat xss).
          { rewrite H. reflexivity. }
          assert (A2 : concat ((a :: s1) :: yss) = a :: (s1 ++ (concat yss))).
          { simpl. reflexivity. }
          rewrite <- A1 in heq. rewrite A2 in heq. injection heq.
          intros I. symmetry. apply I.
      + unfold not. intros C. discriminate.
  }
  {
    generalize dependent s. induction r; intros s H.
    - inv H.
    - inv H.
    - simpl in H. destruct (Sigma_dec t a); inv H. apply MChar.
    - simpl in H. destruct (nullable r1) eqn:E.
      + inv H.
        * inv H2. replace (a :: s1 ++ s2) with ((a :: s1) ++ s2).
          apply MApp.
          -- apply IHr1. apply H3.
          -- apply H4.
          -- reflexivity.
        * symmetry in E. apply nullable_bridge in E. rewrite <- nil_left with (s := (a :: s)).
          apply MApp.
          -- apply E.
          -- apply IHr2. apply H1.
      + inv H.
        * replace (a :: s1 ++ s2) with ((a :: s1) ++ s2).
          apply MApp.
          -- apply IHr1. apply H3.
          -- apply H4.
          -- reflexivity.
    - inv H.
      + apply MUnionL. apply IHr1. apply H2.
      + apply MUnionR. apply IHr2. apply H1.
    - simpl in H. inv H. replace (a :: s1 ++ s2) with ((a :: s1) ++ s2).
      + apply MStarApp.
        * apply IHr. apply H3.
        * apply H4.
      + reflexivity.
  }
Qed.

Theorem match_iff_matchb : forall(s : String) (r : regex),
    true = exp_matchb s r <-> exp_match s r.
Proof.
  intros s r. split.
  {
    generalize dependent r. induction s; intros r H.
    - simpl in H. apply nullable_bridge. apply H.
    - apply der_match. apply der_matchb in H. apply IHs. apply H.
  }
  {
    generalize dependent r. induction s; intros r H.
    - simpl. apply nullable_bridge. apply H.
    - apply der_match in H. apply der_matchb. apply IHs in H. apply H.
  }
Qed.
