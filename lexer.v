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
   Each element in this list of triples will be of the form ((a, re, fsm), pre, suff).
   The tokens can be extracted as (a, pref), where a is the label/action and 
     pre is the labeled word.

   The additional elements in the triple might be helpful for correctness.

   0. None will be returned iff atleast one of the following is occurs:
      a. No rules are provided
      b. No maximal prefix exists
      c. The maximal prefix is empty
   In all cases where an error is not thrown:
   1. forall s, exp_match s re <-> accepting s fsm
   2. exp_match pref re OR accepting pref fsm (equivalent, but which?)
   3. the concatention of all pre is equal to code
   4. If suff = x ++ y, then pre ++ x does not match any of the regular expressions from rules
 *)
Definition State : Type := regex.
Definition transition : Sigma -> State -> State := derivative.
Definition accepts : String -> State -> bool := exp_matchb.
Definition accepting : State -> bool:= nullable.
Definition init_state (r : regex) : State := r.
Definition absorbing_state := EmptySet.
(* in eRule, the State would be the initial state of the machine after converting from regex *)
Definition eRule : Type := String * regex * State.
Definition eeToken : Type := eRule * String * String.
Definition eeLexemes : Type := list eeToken.

Inductive is_prefix : String -> String -> Prop :=
  | pref_def p s
         (H1 : exists q, p ++ q = s) :
      is_prefix p s.

Notation "p ++_= s" := (is_prefix p s) (at level 80).

(* Need to replace exp_match with something more general to States *)
(* maybe we can pass the regex AND the State here and add a hypothesis about their equivalence *)
Inductive max_pref : String -> State -> option (String * String) -> Prop :=
| MP0 (s : String) (r : State)
         (H1 : forall cand, ~(cand ++_= s) \/ ~(exp_match cand r)) :
    max_pref s r None
| MP1 (s : String) (r : State) (p q : String)
      (H0 : p ++ q = s)
      (H1 : p ++_= s)
      (H2 : exp_match p r)
      (H3 : forall(cand : String), cand ++_= s
                              -> ((length cand) <= (length p)) \/ ~(exp_match cand r)) :
    max_pref s r (Some (p, q)).


Fixpoint max_pref_fn (s : String) (state : State) : option (String * String):=
  match s with
  (* in a regex approach, accepting := nullable *)
  | [] => if accepting state then Some ([],[]) else None
  | a :: s' =>
    let
      (* in a regex approach, transition := derivative *)
      state' := transition a state in
    let
      mpxs := max_pref_fn s' state' in
    
    match mpxs with
    | None => if (accepting state') then Some ([a], s') else
               if (accepting state) then Some ([], s) else
                 None
    | Some (p, q) => Some (a :: p, q)
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
      * destruct (accepting fsm).
        -- injection H. intros I1 I2. rewrite I1. rewrite I2. reflexivity.
        -- discriminate.
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

(* It looks like I'm starting to lose some of the modularity. Aside from using exp_match
   directly in the spec instead of something equivalent for States (instead of regexes),
   I am also relying on unfolding accepting as nullable and applying nullable_bridge in this
   proof. I knew at some point I would need to plug the concrete implementation into the lexer,
   but this might not be close enough to the surface to be doing it here. *)
Theorem max_pref_spec_eq_fn : forall(code : String) (fsm : State),
    max_pref code fsm (max_pref_fn code fsm).
Proof.
  induction code; intros fsm.
  (* base case pretty trivial *)
  - simpl. destruct (accepting fsm) eqn:E0.
    + simpl. apply MP1.
      * reflexivity.
      * apply pref_def. exists []. reflexivity.
      * unfold accepting in E0. apply nullable_bridge. symmetry. apply E0.
      * intros cand H. destruct cand.
        -- left. simpl. omega.
        -- inv H. destruct H1. discriminate.
    + simpl. apply MP0. induction cand.
      * right. unfold not. intros C. apply nullable_bridge in C.
        unfold accepting in E0. rewrite E0 in C. discriminate.
      * left. unfold not. intros C. inv C. destruct H1. discriminate.
  (* inductive case ~~slightly~~ more challenging *)
  - specialize (IHcode (transition a fsm)). (* IH only useful when used this way *)
    destruct (max_pref_fn code (transition a fsm)) eqn:E.
    (* if code has a prefix, the proof is pretty straight forward. 
       Add a to the front of that prefix, apply MP1, and do some case analysis. *)
    + destruct p.
      replace ((max_pref_fn (a :: code) fsm)) with (Some ((a :: s), s0)).
      * apply MP1.
        -- symmetry in E.  apply max_pref_fn_splits in E. rewrite E. reflexivity.
        -- inv IHcode. inv H3. destruct H1. apply pref_def.
           exists x. simpl. rewrite H. reflexivity.
        -- inv IHcode. apply match_iff_matchb. simpl. apply match_iff_matchb in H5. apply H5.
        -- intros cand H. inv IHcode. destruct cand.
           ++ left. simpl. omega.
           ++ inv H. destruct H1. injection H. intros I1 I2. rewrite I2.
              simpl. specialize (H7 cand). assert (A1 : cand ++_= s ++ s0).
              { apply pref_def. exists x. apply I1. }
              apply H7 in A1. destruct A1.
              ** left. omega.
              ** right. unfold not. intros C. unfold not in H0. destruct H0.
                 apply match_iff_matchb. apply match_iff_matchb in C.
                 simpl in C. unfold transition. apply C.
      * simpl. destruct (max_pref_fn code (transition a fsm)).
        -- destruct p. simpl. simpl in E.
           injection E. intros I1 I2. rewrite I1. rewrite I2. reflexivity.
        -- simpl in E. discriminate.
    (* 
       This case on the other hand is more complicated because even if code has no prefix,
       there are still two possible prefixes for a :: code (as well as maybe no prefix). 
       We show that these possibilities are exhaustive and do case analysis on them. 
       Within these cases the proofs are pretty straightforward, just lots of case analysis.       
     *)
    + assert (A1 : 
                max_pref_fn (a :: code) fsm = None
                \/ max_pref_fn (a :: code) fsm = Some ([], (a :: code))
                \/ max_pref_fn (a :: code) fsm = Some ([a], code)
             ).
      {
        destruct code. 
        - simpl in E. simpl. destruct (accepting (transition a fsm)). discriminate.
          destruct (accepting fsm).
          + right. left. reflexivity.
          + left. reflexivity.
        - simpl in E. simpl.
          destruct (max_pref_fn code (transition s (transition a fsm))) eqn:E1.
          + destruct p. discriminate.
          + destruct (accepting (transition s (transition a fsm))) eqn:E2. discriminate.
            * destruct (accepting (transition a fsm)) eqn:E3.
              -- discriminate.
              -- inv IHcode. destruct (accepting fsm).
                 ++ right. left. reflexivity.
                 ++ left. reflexivity.
      }
      destruct A1.
      {
        rewrite H. simpl in H.
        assert (A2 : accepting (transition a fsm) = false /\ accepting fsm = false).
        {
          rewrite E in H.
          destruct (accepting (transition a fsm)); destruct (accepting fsm);
            try (discriminate); try (split; reflexivity).
        }
        destruct A2. clear H. inv IHcode. apply MP0. destruct cand.
        - right. unfold not. intros C.
          apply nullable_bridge in C. unfold accepting in H1. rewrite H1 in C. discriminate.
        - specialize (H2 cand). destruct H2.
          + left. unfold not. intros C. unfold not in H. destruct H.
            inv C. destruct H2. apply pref_def. exists x. injection H.
            intros I1 I2. apply I1.
          + destruct (Sigma_dec a s).
            * right. unfold not. intros C. unfold not in H. destruct H.
              apply match_iff_matchb. apply match_iff_matchb in C.
              unfold transition. unfold transition in C. simpl. simpl in C.
              rewrite e. apply C.
            * left. unfold not. intros C. inv C. destruct H2.
              injection H2. intros I1 I2. rewrite I2 in n. contradiction.
      }
      destruct H.
      {
        rewrite H. simpl in H.
        assert (A2 : accepting (transition a fsm) = false /\ accepting fsm = true).
        {
          rewrite E in H.
          destruct (accepting (transition a fsm)); destruct (accepting fsm);
            try (discriminate); try (split; reflexivity).
        }
        destruct A2. clear H. inv IHcode. apply MP1.
        - reflexivity.
        - apply pref_def. exists (a :: code). reflexivity.
        - apply match_iff_matchb. simpl. unfold accepting in H1. symmetry. apply H1.
        - intros cand H. destruct cand.
          + left. omega.
          + right. inv H. destruct H3. injection H. intros I1 I2.
            specialize (H2 cand). destruct H2.
            * unfold not in H2. destruct H2. apply pref_def. exists x. apply I1.
            * rewrite I2. unfold not. intros C. unfold not in H2. destruct H2.
              apply match_iff_matchb. apply match_iff_matchb in C. simpl in C. apply C.
      }
      {
        rewrite H. simpl in H.
        assert (A2 :  accepting (transition a fsm) = true).
        {
          rewrite E in H.
          destruct (accepting (transition a fsm)); destruct (accepting fsm);
            try (discriminate); try (split; reflexivity).
        }
        clear H. inv IHcode. apply MP1.
        - reflexivity.
        - apply pref_def. exists code. reflexivity.
        - apply match_iff_matchb. simpl. unfold accepting in A2. unfold transition in A2.
          symmetry. apply A2.
        - intros cand H. destruct cand.
          + left. simpl. omega.
          + destruct cand.
            * left. simpl. omega.
            * right. inv H. destruct H0. injection H. intros I1 I2.
              specialize (H1 (s0 :: cand)). destruct H1.
              -- unfold not in H0. destruct H0. apply pref_def. exists x. inv H. simpl. apply H2.
              -- unfold not. intros C. unfold not in H0. destruct H0.
                 apply match_iff_matchb. apply match_iff_matchb in C.
                 simpl in C. simpl. rewrite <- I2. apply C.
      }
Qed.
        
Definition extract_fsm_for_max (code : String) (eru : eRule) :=
  match eru with
    (_, _, fsm) => (eru, max_pref_fn code fsm)
  end.

Definition max_prefs (code : String) (erules : list eRule) :=
    map (extract_fsm_for_max code) erules.

Definition longer_pref (apref1 apref2 : eRule * (option (String * String))) :=
  match apref1, apref2 with
  | (_, None), (_, _) => apref2
  | (_, _), (_, None) => apref1
  | (_, Some (x, _)), (_, Some (y, _)) => if (length y) <? (length x)
                                         then apref2 else apref1
  end.

Fixpoint max_of_prefs (mprefs : list (eRule * (option (String * String)))) :=
  match mprefs with
  | [] => (([], EmptySet, EmptySet), @None (String * String))
  | p :: ps => longer_pref p (max_of_prefs ps)
  end.

(* interesting that no induction was required here *)
Lemma max_first_or_rest : forall ys x y,
    x = max_of_prefs (y :: ys) -> x = y \/ x = max_of_prefs ys.
Proof.
  intros ys x y H. simpl in H. destruct y.
  destruct o; unfold longer_pref in H; destruct (max_of_prefs ys).  
  - destruct p. destruct o.
    + destruct p. destruct (length s1 <? length s).
      * right. apply H.
      * left. apply H.
    + left. apply H.
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
          | (eru, Some (prefix, suffix)) => match (lex rules suffix) with
                                                | None => None
                                                | Some lexemes =>
                                                  Some ( (eru, prefix, suffix) :: lexemes )
                                                end
          end
        end
  end.
Next Obligation.
  assert (A0 : prefix <> []).
  { unfold not. intros C. rewrite C in H1. specialize (H1 (l, r0, r)). specialize (H1 suffix).
    contradiction. }
  assert (A2 : exists(fsm : State), Some (prefix, suffix) = max_pref_fn code fsm).
  { (* this should follow from Heq_mpref *)
    induction rules. contradiction.
    simpl in Heq_mpref. apply max_first_or_rest in Heq_mpref. destruct Heq_mpref.
    - destruct a in H2. exists(init_state r1). injection H2. intros I1 I2 I3 I4. apply I1.
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
  
                 
  
  
