(* Use the built-in List module instead of the one from
   Software Foundations, so that we have access to all
   of the predefined lemmas *)
Require Import List.
Import ListNotations.

(* Regex definition from Software Foundations *)
Inductive reg_exp {T : Type} : Type :=
| EmptySet
| EmptyStr
| Char (t : T)
| App (r1 r2 : reg_exp)
| Union (r1 r2 : reg_exp)
| Star (r : reg_exp).

(* Regex spec from Software Foundations *)
Inductive exp_match {T} : list T -> reg_exp -> Prop :=
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

Hint Constructors exp_match : core.

Notation "s =~ re" := (exp_match s re) (at level 80).

Ltac inv H := inversion H; subst; clear H.

Lemma star_concat :
  forall T s r',
    exp_match s (Star r')
    -> (exists xss : list (list T),
           s = concat xss
           /\ (forall xs,
                  In xs xss
                  -> exp_match xs r')).
Proof.
  intros T s r' hm.
  remember (Star r') as r. generalize dependent r'. 
  induction hm; intros r' heq; inv heq.
  - exists []; split; auto.
    intros xs hi; inv hi.
  - destruct (IHhm2 r') as (xss' & heq & hall); subst; auto.
    exists (s1 :: xss'); split; auto.
    intros xs hi.
    destruct hi as [hh| ht]; subst; auto.
Qed.

Lemma concat_singleton :
  forall X (x : X) xss,
    [x] = concat xss
    -> In [x] xss.
Proof.
  intros X x xss; induction xss as [| xs xss IH]; intros heq; simpl in *.
  - inv heq.
  - destruct xs as [| x' xs]; simpl in *; auto.
    inv heq.
    symmetry in H1; apply app_eq_nil in H1.
    destruct H1; subst. auto.
Qed.

Lemma from_your_email :
  forall T (a : T) r,
    exp_match [a] (Star r) -> exp_match [a] r.
Proof.
  intros T a r hm.
  eapply star_concat in hm; eauto.
  destruct hm as (xss & heq & hall).
  apply hall.
  apply concat_singleton. auto.
Qed.
