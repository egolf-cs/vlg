Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.NatInt.NZOrder.

From VLG Require Import ltac.
From VLG Require Import coredefs.
From VLG Require Import spec.
From VLG Require Import prefixer.

Lemma acc_recursive_call :
  forall code rules label s l suffix,
    Acc lt (length code)
    -> max_of_prefs (max_prefs code rules) = (label, Some (s :: l, suffix))
    -> Acc lt (length suffix).
Proof.
  intros code rules label s l suffix Ha Heq.
  apply Acc_inv with (x := length code).
  - apply Ha.
  - assert(A2 : exists(fsm : State), Some (s :: l, suffix) = max_pref_fn code fsm).
    {
      induction rules.
      - simpl in Heq. discriminate.
      - symmetry in Heq. apply max_first_or_rest in Heq. destruct Heq.
        + destruct a. simpl in H. exists s0. injection H; intros; subst. apply H0.
        + apply IHrules. destruct rules.
          * simpl in H. discriminate.
          * rewrite H. reflexivity.
    }
    assert(A3 : s :: l <> []).
    { intros C. discriminate. }
    destruct A2 as (fsm & A2).
    apply proper_suffix_shorter with (suffix := suffix) (code := code) (fsm := fsm) in A3.
    + apply A3.
    + apply A2.
Defined.

Fixpoint lex'
         (rules : list sRule)
         (code : String)
         (Ha : Acc lt (length code))
         {struct Ha} : (list Token) * String :=
  match max_of_prefs (max_prefs code rules) as mpref'
        return max_of_prefs (max_prefs code rules) = mpref' -> _
  with
  | (_, None) => fun _ => ([], code) (* Code cannot be processed further *)
  | (_, Some ([], _)) => fun _ => ([], code) (* Code cannot be processed further *)
  | (label, Some (ph :: pt, suffix)) =>
    fun Heq =>
      match (lex' rules suffix
                  (acc_recursive_call _ _ _ _ _ _ Ha Heq)) with
      | (lexemes, rest) => (((label, ph :: pt) :: lexemes), rest)
      end
  end eq_refl.
(**)

Definition init_srule (rule : Rule) : sRule :=
  match rule with
  | (label, re) => (label, init_state re)
  end.

Definition lex (rules : list Rule) (code : String) :=
  let
    srules := map init_srule rules
  in
  lex' srules code (lt_wf _).
