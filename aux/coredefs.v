Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.NatInt.NZOrder.

From VLG Require Import matcher.
From VLG Require Import ltac.

Definition Sigma := matcher.Sigma.
Definition Sigma_dec := matcher.Sigma_dec.
Definition String := matcher.String.

Lemma String_dec : forall s s' : String, {s = s'} + {s <> s'}.
Proof. decide equality. apply Sigma_dec. Qed.

Definition State : Type := regex.
Definition transition : Sigma -> State -> State := derivative.
Definition accepts : String -> State -> bool := exp_matchb.
Definition accepting : State -> bool:= nullable.

Lemma accepts_nil: forall(fsm : State),
    accepting fsm = accepts [] fsm.
Proof.
  intros fsm. reflexivity.
Qed.

Lemma accepts_transition : forall cand a fsm,
    accepts cand (transition a fsm)
    = accepts (a :: cand) fsm.
Proof.
  auto.
Qed.

Inductive eq_models : State -> regex -> Prop :=
| SReq (fsm : State) (r : regex)
       (H1 : forall(s : String), true = accepts s fsm <-> exp_match s r) :
    eq_models fsm r.

Definition init_state (r : regex) : State := r.
Definition init_state_inv (fsm : State) : regex := fsm.
(** Facts about inverting init_state **)
Lemma invert_init_correct' : forall(r : regex) (s : String),
    exp_match s (init_state_inv (init_state r)) <-> exp_match s r.
Proof.
  intros. split; auto.
Qed.

Definition Label : Type := String.
Definition Prefix : Type := String.
Definition Suffix : Type := String.
Definition Token : Type := Label * Prefix.
Definition Rule : Type := Label * regex.

Lemma ru_dec : forall (ru1 ru2 : Rule), {ru1 = ru2} + {ru1 <> ru2}.
Proof.
  intros. destruct ru1. destruct ru2.
  destruct (String_dec l l0); destruct (regex_dec r r0); subst; auto;
    right; intros C; destruct n; inv C; auto.
Qed.

Definition sRule : Type := Label * State.

(** Facts about accepts/accepting **)
Lemma accepts_matches : forall(s : String) (fsm : State),
    true = accepts s fsm <-> exp_match s (init_state_inv fsm).
Proof.
  intros. split; intros; apply match_iff_matchb; auto.
Qed.

(* no external depends after this *)
Lemma accepting_nilmatch : forall fsm,
    true = accepting fsm
    <-> exp_match [] (init_state_inv fsm).
Proof.
  intros. split; intros.
  - apply accepts_matches. rewrite <- accepts_nil. auto.
  - apply accepts_matches in H. rewrite accepts_nil. auto.
Qed.

Lemma inv_eq_model : forall(fsm : State),
    eq_models fsm (init_state_inv fsm).
Proof.
  intros fsm. apply SReq. intros s. rewrite accepts_matches. split; auto.
Qed.

Lemma inv_transition : forall cand a fsm,
    exp_match cand (init_state_inv (transition a fsm))
    <-> exp_match (a :: cand) (init_state_inv fsm).
Proof.
  intros. repeat rewrite <- accepts_matches. rewrite accepts_transition.
  split; auto.
Qed.
