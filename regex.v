Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.

Ltac inv H := inversion H; subst; clear H.

(* Borrowed these from another paper, actually about regex derivatives *)
Variable Sigma : Type.
Variable x : Sigma.
Variable y : Sigma.
Variable z : Sigma.
Variable Sigma_dec : forall (c c': Sigma), {c = c'} + {c <> c'}.
Axiom Sigma_dec_refl : forall(T : Type) (p1 p2 : T) (a : Sigma), p1 = if Sigma_dec a a then p1 else p2.
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
  (* | MStarChar a re
                 (H1 : exp_match [a] re) :
      exp_match [a] (Star re) *)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
      exp_match (s1 ++ s2) (Star re).

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
  | App r1 r2 =>  Union (App (derivative a r1) r2) (App (nullify r1) (derivative a r2))
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

Lemma singleton_app : forall(a : Sigma) (s1 s2 : String),
    s1 ++ s2 = [a] -> (s1 = [a] /\ s2 = []) \/ (s1 = [] /\ s2 = [a]).
Proof.
Admitted.

Lemma mute_nullify : forall(r : regex),
    nullable (nullify r) = nullable r.
Proof.
Admitted.

Lemma Star_empty_empty : forall(s : String),
    exp_match s (Star EmptyStr) -> s = [].
Proof.
Admitted.

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

Lemma foo0 : forall(s : String) (r : regex),
    exp_match s r -> exp_match s (Star r).
Proof.
  intros s. induction s; intros r H.
  - apply MStar0.
  - rewrite <- nil_right with (s := a::s). apply MStarApp.
    + apply H.
    + apply MStar0.
Qed.
  
Lemma foo1 : forall(a : Sigma) (r1 r2 : regex),
    exp_match [a] (Star (App r1 r2)) ->
    (exp_match [a] r1) \/
    (exp_match [a] r2).
Proof.
Admitted.

Lemma foo2 : forall(a : Sigma) (r1 r2 : regex),
    exp_match [a] (Star (App r1 r2)) ->
    (exp_match [a] r1 -> exp_match [] r2) /\
    (exp_match [a] r2 -> exp_match [] r1).
Proof.
  intros a r1 r2 H. split; intros H1.
  - inv H.
    apply singleton_app in H0. destruct H0; destruct H.
    + rewrite H in H3. inv H3. inv H4
    + rewrite H in H3. Admitted.

Theorem singleton_star_app : forall(a : Sigma) (r1 r2 : regex),
    exp_match [a] (Star (App r1 r2)) ->
    (exp_match [a] (Star r1) /\ exp_match [] r2) \/
    (exp_match [a] (Star r2) /\ exp_match [] r1).
Proof.
  intros a r1 r2 H.
  assert(H1 := H).
  apply foo1 in H. apply foo2 in H1.
  destruct H1. destruct H; assert(H2 := H); apply foo0 in H2.
  - left. split.
    + apply H2.
    + apply H0. apply H.
  - right. split.
    + apply H2.
    + apply H1. apply H.
Qed.

Lemma singleton_star : forall(a : Sigma) (r : regex),
    exp_match [a] (Star r) -> exp_match [a] r.
Proof.
  intros a r H. induction r.
  - inv H. inv H2.
  - inv H. apply singleton_app in H1. destruct H1; destruct H.
    + rewrite H in H2. inv H2.
    + apply Star_empty_empty in H3. rewrite H0 in H3. discriminate.
  - inv H. apply singleton_app in H1. destruct H1; destruct H.
    + rewrite H in H2. rewrite H. rewrite H0. simpl. apply H2.
    + rewrite H0 in H3. inv H3. inv H2.
  - apply singleton_star_app in H. destruct H; destruct H.
    + rewrite <- nil_right with (s := [a]). apply MApp.
      * apply IHr1. apply H.
      * apply H0.
    + rewrite <- nil_left with (s := [a]). apply MApp.
      * apply H0.
      * apply IHr2. apply H.
  - Admitted.
                     
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
    generalize dependent r. induction s; intros r H.
    - apply nullable_bridge. induction r.
      + inv H.
      + inv H.
      + simpl. destruct (Sigma_dec t a).
        * simpl. reflexivity.
        * inv H. contradiction.
      + inv H. apply singleton_app in H1.
        destruct H1; destruct H; rewrite H in H3; rewrite H0 in H4.
        * apply nullable_bridge in H4. apply IHr1 in H3.
          simpl. rewrite <- H3. rewrite <- H4.
          destruct (andb (nullable (nullify r1)) (nullable (derivative a r2))); simpl; reflexivity.
        * apply nullable_bridge in H3. apply IHr2 in H4.
          simpl. rewrite mute_nullify. rewrite <- H3. rewrite <- H4.
          destruct (andb (nullable (derivative a r1)) (nullable r2)); simpl; reflexivity.
      + inv H.
        * simpl. apply IHr1 in H2. rewrite <- H2.
          destruct (nullable (derivative a r2)); simpl; reflexivity.
        * simpl. apply IHr2 in H1. rewrite <- H1.
          destruct (nullable (derivative a r1)); simpl; reflexivity.
      + 

        simpl. apply singleton_star in H. apply IHr in H. rewrite <- H. reflexivity.
    - 
  }
  {
    admit.
  }
Admitted.

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

