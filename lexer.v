Require Import Ascii.
Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.

From VLG Require Import regex.

Definition Sigma := regex.Sigma.
Definition Sigma_dec := regex.Sigma_dec.
Definition String := regex.String.

Definition Rule : Type := String * regex.
Definition Token : Type := String * String.
Definition eToken : Type := Rule * String * String.
Definition eLexemes : Type := list eToken.
(* 
   The lexer will accept a list of pairs and a string.
   Each element in this list of pairs will contain a regex and its corresponding label/action.

   The function will return a list of triples.
   Each element in this list of triples will be of the form ((a, re), pre, suff).
   The tokens can be extracted as (a, pref), where a is the label/action and 
     pre is the labeled word.

   The additional elements in the triple might be helpful for correctness.

   0. An error will be thrown <-> the code could not be lexed entirely according to the rules
   In all cases where an error is not thrown:
   1. exp_match pref re
   2. the concatention of all pre is equal to code
   3. If suff = x ++ y, then pre ++ x does not match any of the regular expressions from rules
 *)

(*********************************************
*
*
*   Alternative formulation, more modular.
*
*
*********************************************)
Definition State : Type := regex.
Definition transition : Sigma -> State -> State := derivative.
Definition accepting : State -> bool:= nullable.
Definition init_state (r : regex) : State := r.
Definition absorbing_state := EmptySet.
(* in eRule, the State would be the initial state of the machine after converting from regex *)
Definition eRule : Type := String * regex * State.
Definition eeToken : Type := eRule * String * String.
Definition eeLexemes : Type := list eeToken.

Fixpoint max_pref_fn (s : String) (state : State) : option (String * String):=
  match s with
  (* in a regex approach, accepting := nullable *)
  | [] => if accepting state then Some ([],[]) else None
  | a :: s' =>
    let
      (* in a regex approach, transition := derivative *)
      state' := transition a state in
    let
      (* if (p, s'') is a prefix, suffix pair for s', then (a::p, s'') is a pair for a::s' *)
      mpxs := max_pref_fn s' state' in
    
    match mpxs with
    | None => if (accepting state') then Some ([a], s') else None
    | Some (p, s'') => Some (a :: p, s'')
    end
  end.

Lemma max_pref_fn_splits : forall(code prefix suffix : String) (fsm : State),
    Some (prefix, suffix) = max_pref_fn code fsm -> code = prefix ++ suffix.
Proof.
  induction code as [| a s']; intros prefix suffix fsm H.
  - simpl in H. destruct (accepting fsm).
    + injection H. intros I1 I2. rewrite I1. rewrite I2. reflexivity.
    + discriminate.
  - simpl in H. destruct (max_pref_fn s' (transition a fsm)) eqn:E1.
    + destruct p as [s0 s1]. injection H. intros I1 I2. rewrite I1. rewrite I2.
      assert (A : s' = s0 ++ s1 -> a :: s' = (a :: s0) ++ s1).
      { intros HA. rewrite HA. reflexivity. }
      apply A. apply IHs' with (fsm := (transition a fsm)).
      * symmetry. apply E1.
    + destruct (accepting (transition a fsm)).
      * injection H. intros I1 I2. rewrite I1. rewrite I2. reflexivity.
      * discriminate.
Qed.

Lemma proper_suffix_shorter : forall(code prefix suffix : String) (fsm : State),
  prefix <> []
  -> Some (prefix, suffix) = max_pref_fn code fsm
  -> length suffix < length code.
Proof.
  intros code prefix suffix fsm. intros Hneq Heq.
  apply max_pref_fn_splits in Heq. rewrite Heq.
  replace (length (prefix ++ suffix)) with ((length prefix) + (length suffix)).
  - apply Nat.lt_add_pos_l. destruct prefix.
    + contradiction.
    + simpl. omega.
  - symmetry. apply app_length.
Qed.

Definition extract_fsm_for_max (code : String) (eru : eRule) :=
  match eru with
    (_, _, fsm) => (Some eru, max_pref_fn code fsm)
  end.

Definition max_prefs (code : String) (erules : list eRule) :=
    map (extract_fsm_for_max code) erules.

Definition longer_pref (apref1 apref2 : (option eRule) * (option (String * String))) :=
  match apref1, apref2 with
  | (_, None), (_, _) => apref2
  | (_, _), (_, None) => apref1
  | (_, Some (x, _)), (_, Some (y, _)) => if (length y) <? (length x)
                                         then apref2 else apref1
  end.

Fixpoint max_of_prefs (mprefs : list ((option eRule) * (option (String * String)))) :=
  match mprefs with
  | [] => (@None eRule, @None (String * String))
  | p :: ps => longer_pref p (max_of_prefs ps)
  end.

(* interesting that no induction was required here *)
Lemma max_first_or_rest : forall ys x y,
    x = max_of_prefs (y :: ys) -> x = y \/ x = max_of_prefs ys.
Proof.
  intros ys x y H. simpl in H. destruct y.
  destruct o; destruct o0; unfold longer_pref in H; destruct (max_of_prefs ys).  
  - destruct o0.
    + destruct p. destruct p0. destruct (length s1 <? length s).
      * right. apply H.
      * left. apply H.
    + destruct p. left. apply H.
  - right. apply H.
  - destruct o0.
    + destruct p. destruct p0. destruct (length s1 <? length s).
      * right. apply H.
      * left. apply H.
    + destruct p. left. apply H.
  - right. apply H.
Qed.
    
Program Fixpoint lex (rules : list Rule) (code : String)
        {measure (length code)} : option (list eeToken) :=
  match code with
  | [] => Some []
  | _ => match rules with
        | [] => None (* must have rules *)
        | _ =>
          let
            erules := map (fun ru => match ru with
                                    (a,re) => (a, re, init_state re)
                                  end) rules
          in
          let (* find all the maximal prefixes, associating them with a rule as we go *)
            mprefs := max_prefs code erules
          in
          let (* of these maximal prefixes, find the longest *)
            mpref := max_of_prefs mprefs
          in
          match mpref with
          | (_, None) => None (* This state suggests malformed code *)
          | (_, Some ([], _)) => None (* Longest match empty-> non-terminating-> malformed code *)
          | (None, _) => None (* This state shouldn't be reachable *)
          | (Some eru, Some (prefix, suffix)) => match (lex rules suffix) with
                                                | None => None
                                                | Some lexemes =>
                                                  Some ( (eru, prefix, suffix) :: lexemes )
                                                end
          end
        end
  end.
Next Obligation.
  assert (A0 : prefix <> []).
  { unfold not. intros C. rewrite C in H1. specialize (H1 (Some eru)). specialize (H1 suffix).
    contradiction. }
  assert (A2 : exists(fsm : State), Some (prefix, suffix) = max_pref_fn code fsm).
  { (* this should follow from Heq_mpref *)
    induction rules. contradiction.
    simpl in Heq_mpref. apply max_first_or_rest in Heq_mpref. destruct Heq_mpref.
    - destruct a in H2. exists(init_state r). injection H2. intros I1 I2. apply I1.
    - apply IHrules.
      + destruct rules.
        * simpl in H2. discriminate.
        * unfold not. intros C. discriminate.
      + apply H2.
  }
  destruct A2 as [fsm].
  apply proper_suffix_shorter with (suffix := suffix) (code := code) (fsm := fsm) in A0.
  - apply A0.
  - apply H2.
Qed.
  
                 
  
  
