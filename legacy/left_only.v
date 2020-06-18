Require Import List.
Import ListNotations.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.

(* Borrowed these from another paper, actually about regex derivatives *)
Variable Sigma : Type.
Variable Sigma_dec : forall (c c': Sigma), {c = c'} + {c <> c'}.

(* Didn't bother with Intersection and Complement yet *)
Inductive reg_exp : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : Sigma)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Fixpoint nullify (r : reg_exp) :=
  match r with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char _ => EmptyStr
  (* slightly different from paper, but equivalent I think *)
  | App r1 r2 => match nullify r1, nullify r2 with 
                | EmptyStr, EmptyStr => EmptyStr
                | _, _ => EmptySet
                end
  (* slightly different from paper, but equivalent I think *)
  | Union r1 r2 => match nullify r1, nullify r2 with
                  | EmptySet, EmptySet => EmptySet
                  | _, _ => EmptyStr
                  end
  | Star _ => EmptyStr
  end.

Fixpoint derivative (a : Sigma) (r : reg_exp) :=
  match r with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char x => if Sigma_dec x a then EmptyStr else EmptySet
  | App r1 r2 =>  Union (App (derivative a r1) r2) (App (nullify r1) (derivative a r2))
  | Union r1 r2 => Union (derivative a r1) (derivative a r2)
  | Star r => App (derivative a r) (Star r)
  end.

(* a measure will need to go here *)(*
Definition mu' (c : Sigma) (r : reg_exp) := 0.
                 

(* This program would recursively take derivatives with respect to the same symbol *)
Program Fixpoint der_it (a : Sigma) (r : reg_exp) {measure (mu' a r)} :=
  match r with
  (* Might need Not(EmptySet) and Not(EmptyStr) as base cases if we extend to Complement *)
  | EmptySet => EmptySet
  | EmptyStr => EmptyStr
  | _ => der_it a (derivative a r) (* Might need to do something special with App and Star *)
  end.
Next Obligation.
Abort.*)

Fixpoint mu (r : reg_exp) := 
  match r with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | Union r _
  | App r _
  | Star r => (mu r)
  end.

Fixpoint rec_left (r : reg_exp) :=
  match r with
  | EmptySet => EmptySet
  | EmptyStr => EmptyStr
  | Char t => Char t
  | App r _
  | Union r _
  | Star r => rec_left r
  end.

Definition mu_s (r : reg_exp) := mu (rec_left r).

(* These 3 lemmas are useful for avoiding unfolding mu_s in recursive cases of der_decreasing *)
Lemma mu_s_left_U : forall(r1 r2 : reg_exp), mu_s (Union r1 r2) = mu_s r1.
Proof.
  intros r1 r2. unfold mu_s. simpl. reflexivity.
Qed.

Lemma mu_s_left_App : forall(r1 r2 : reg_exp), mu_s (App r1 r2) = mu_s r1.
Proof.
  intros r1 r2. unfold mu_s. simpl. reflexivity.
Qed.

Lemma mu_s_rec_Star : forall(r : reg_exp), mu_s (Star r) = mu_s r.
Proof.
  intros r. unfold mu_s. simpl. reflexivity.
Qed.

(* mu decreases relative to a regex when applied to that regex's derivative *)
(** I made the mistake of using rec_left in the hypotheses. It should be just r (or whatever I'm matching with in der_sub_all) **)
Theorem der_decreasing' : forall(a : Sigma) (r : reg_exp), rec_left r <> EmptySet -> rec_left r <> EmptyStr -> (mu_s (derivative a r)) < (mu_s r).
Proof.
  intros a r. induction r; intros Hset Hstr; try(contradiction).
  - unfold mu_s. destruct (Sigma_dec t a) eqn:E; simpl; rewrite E; simpl; omega.
  - simpl. rewrite mu_s_left_U. repeat rewrite mu_s_left_App.
    apply IHr1. simpl in Hset. apply Hset. simpl in Hstr. apply Hstr.
  - simpl. repeat rewrite mu_s_left_U.
    apply IHr1. simpl in Hset. apply Hset. simpl in Hstr. apply Hstr.
  - simpl. rewrite mu_s_left_App. repeat rewrite mu_s_rec_Star.
    apply IHr. simpl in Hset. apply Hset. simpl in Hstr. apply Hstr.
Qed.

Fixpoint simplify (r : reg_exp) :=
  match r with
  | App EmptySet _ => EmptySet
  | App r1 r2 => match simplify r1 with
                | EmptySet => EmptySet
                | _ => r
                end
  | Star EmptySet => EmptyStr
  | _ => r
  end.

Lemma simplify_empty_app : forall(r1 r2 : reg_exp), EmptySet = simplify r1 -> EmptySet = simplify (App r1 r2).
Proof.
  intros r1 r2 H. simpl. rewrite <- H. destruct r1; reflexivity.
Qed.

Theorem der_decreasing : forall(a : Sigma) (r : reg_exp), EmptySet <> simplify r -> (mu_s (derivative a r)) < (mu_s r).
Proof.
  intros a r. induction r; intros Hset.
  - contradiction.
  - unfold mu_s. simpl. omega.
  - unfold mu_s. destruct (Sigma_dec t a) eqn:E; simpl; rewrite E; simpl; omega.
  - simpl. rewrite mu_s_left_U. repeat rewrite mu_s_left_App. apply IHr1.
    + unfold not. intros C. apply simplify_empty_app with (r2 := r2) in C. contradiction.
  - simpl. repeat rewrite mu_s_left_U. apply IHr1.
    + admit. (* cannot reach contradiction *)
  - rewrite mu_s_rec_Star. apply IHr. simpl in Hset. (* cannot reach contradiction *)
Admitted.
(* I no longer think recursing only on the left will work *)


(* This program would explore the entire tree of subsequent derivatives, 
where each branch is a character in the alphabet abet *)
Program Fixpoint der_sub_all (abet : list Sigma) (r : reg_exp) {measure (mu_s r)} : list reg_exp :=
  match simplify r with
  | EmptySet => [EmptySet]
  (* | EmptyStr => [EmptySet] *) (* This is unnecessary and might be causing problems *)
  | _ =>
    (* take the derivative of the regex with respect to all chars *)
    (* find all the derivatives of all these derivatives *)
    flat_map (fun a => (der_sub_all abet (derivative a r))) abet
  end.
Next Obligation. 
  apply der_decreasing. apply H.
Qed.

