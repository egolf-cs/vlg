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
(* Look into Coq record types *)


(* 
   The lexer will accept a list of pairs and a string.
   Each element in this list of pairs will contain a regex and its corresponding label/action.

   The function will return a list of triples.
   Each element in this list of triples will be of the form ((a, re, fsm), pre, suff).
   The tokens can be extracted as (a, pref), where a is the label/action and 
     pre is the labeled word.

   The additional elements in the triple might be helpful for correctness.

   0. None will be returned iff atleast one of the following occurs:
      a. No rules are provided
      b. No maximal prefix exists
      c. The maximal prefix is empty

   In all cases where an error is not thrown:
   1. forall s, exp_match s re <-> accepting s fsm
   3. the concatention of all pre is equal to code

   2. exp_match pref re OR accepting pref fsm (equivalent, but which?)
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
  
(************************************
*
*        Proof of correctness
*
************************************)                 
  

(* This doesn't ~need~ to be inductive *)
Inductive is_prefix : String -> String -> Prop :=
  | pref_def p s
         (H1 : exists q, p ++ q = s) :
      is_prefix p s.

Notation "p ++_= s" := (is_prefix p s) (at level 80).

Lemma app_head_prefix : forall(xs ys : String),
    xs ++_= xs ++ ys.
Proof.
  intros xs ys. apply pref_def. exists ys. reflexivity.
Qed.

Lemma cons_prefix : forall(x y : Sigma) (xs ys : String),
    x :: xs ++_= y :: ys <-> x = y /\ xs ++_= ys.
Proof.
  intros x y xs ys. split; intros H.
  {
    inv H. destruct H1.
    injection H. intros I1 I2. split; subst.
    - reflexivity.
    - apply app_head_prefix.
  }
  {
    destruct H. inv H0. destruct H1.
    apply pref_def. exists x. rewrite <- H. reflexivity.
  }
Qed.

Lemma eq_len_eq_pref : forall(x s p : String),
  length p = length s
  -> s ++_= x
  -> p ++_= x
  -> s = p.
Proof.
  induction x; intros s p Heq Hs Hp .
  - inv Hs. inv Hp. destruct H0. destruct H1.
    apply app_eq_nil in H. destruct H.
    apply app_eq_nil in H0. destruct H0.
    subst. reflexivity.
  - destruct s; destruct p.
    + reflexivity.
    + simpl in Heq. discriminate.
    + simpl in Heq. discriminate.
    + apply cons_prefix in Hs. apply cons_prefix in Hp.
      destruct Hs. destruct Hp. subst.
      assert (length p = length s0).
      { simpl in Heq. omega. }
      apply IHx in H.
      * rewrite H. reflexivity.
      * apply H0.
      * apply H2.
Qed.


(* Need to replace exp_match with something more general to States *)
(* maybe we can pass the regex AND the State here and add a hypothesis about their equivalence *)
Inductive no_max_pref : String -> State -> Prop :=
| MP0 (s : String) (r : State)
         (H1 : forall cand, cand ++_= s -> ~(exp_match cand r)) :
    no_max_pref s r.

Inductive max_pref : String -> State -> String -> Prop :=
| MP1 (s : String) (r : State) (p : String)
      (H1 : p ++_= s)
      (H2 : exp_match p r)
      (H3 : forall(cand : String), cand ++_= s
                              -> ((length cand) <= (length p)) \/ ~(exp_match cand r)) :
    max_pref s r p.

Lemma false_not_true : forall(b : bool),
    b = false <-> not(b = true).
Proof.
  intros b. split.
  - intros H. destruct b.
    + discriminate.
    + unfold not. intros C. discriminate.
  - intros H. destruct b.
    + contradiction.
    + reflexivity.
Qed.

Theorem max_pref_correct_None : forall(code : String) (fsm : State),
    no_max_pref code fsm <-> None = max_pref_fn code fsm.
Proof.
  intros code fsm. split.
  {
    generalize dependent fsm; induction code; intros fsm H.
    - simpl. inv H. specialize (H1 []). assert (A : [] ++_= []).
      { apply pref_def. exists []. reflexivity. }
      apply H1 in A. clear H1. destruct (accepting fsm) eqn:E.
      + exfalso. unfold not in A. destruct A. apply nullable_bridge.
        symmetry. unfold accepting in E. apply E.
      + reflexivity.
    - specialize (IHcode (transition a fsm)). inv H.
      assert (A0 : no_max_pref code (transition a fsm)).
      {
        apply MP0. intros cand H. specialize (H1 (a :: cand)).
        assert (A1 : a :: cand ++_= a :: code).
        { apply pref_def. inv H. destruct H0. exists x. rewrite <- H. reflexivity. }
        apply H1 in A1. unfold not. intros C. unfold not in A1. destruct A1.
        apply match_iff_matchb. apply match_iff_matchb in C. simpl. unfold transition in C.
        apply C.
      }
      apply IHcode in A0.
      simpl.
      assert (A1 : accepting (transition a fsm) = false).
      { specialize (H1 [a]). assert (A2 : [a] ++_= a :: code).
        { apply pref_def. exists code. reflexivity. }
        apply H1 in A2. apply false_not_true. unfold not. intros C.
        unfold not in A2. destruct A2. apply match_iff_matchb. simpl.
        unfold accepting in C. unfold transition in C. symmetry. apply C.
      }
      assert (A2 : accepting fsm = false).
      {
        specialize (H1 []). assert (A3 : [] ++_= a :: code).
        { apply pref_def. exists (a :: code). reflexivity. }
        apply H1 in A3. apply false_not_true. unfold not. intros C.
        unfold not in A3. destruct A3. apply nullable_bridge. unfold accepting in C.
        symmetry. apply C.
      } 
      rewrite <- A0. rewrite A1. rewrite A2. reflexivity.
  }
  {
    generalize dependent fsm; induction code; intros fsm H.
    - apply MP0. intros cand H0. simpl in H.
      assert (A0 : accepting fsm = false).
      {
        destruct (accepting fsm).
        - discriminate.
        - reflexivity.
      }
      assert (A1 : cand = []).
      {
        destruct cand.
        - reflexivity.
        - inv H0. destruct H1. discriminate.
      } 
      unfold not. intros C. rewrite A1 in C. apply nullable_bridge in C.
      unfold accepting in A0. rewrite A0 in C. discriminate.
    - specialize (IHcode (transition a fsm)).
      apply MP0. intros cand H0. simpl in H. destruct (max_pref_fn code (transition a fsm)).
      + destruct p. discriminate.
      + assert (A0 : accepting (transition a fsm) = false).
        {
          destruct (accepting (transition a fsm)).
          - discriminate.
          - reflexivity.
        }
        assert (A1 : accepting fsm = false).
        {
          destruct (accepting fsm).
          - rewrite A0 in H. discriminate.
          - reflexivity.
        }
        destruct cand.
        * intros C. apply nullable_bridge in C. unfold accepting in A1.
          rewrite A1 in C. discriminate.
        * destruct (Sigma_dec a s).
          -- rewrite <- e. destruct cand.
             ++ unfold not. intros C. apply match_iff_matchb in C. simpl in C.
                unfold accepting in A0. unfold transition in A0.
                rewrite A0 in C. discriminate.
             ++ assert (A2 : no_max_pref code (transition a fsm)).
                { apply IHcode. reflexivity. }
                inv A2. specialize (H1 (s0 :: cand)). inv H0. destruct H2. injection H0.
                intros I1. assert (A3 :  s0 :: cand ++_= code).
                { apply pref_def. exists x. apply I1. }
                apply H1 in A3. unfold not. intros C. unfold not in A3. destruct A3.
                apply match_iff_matchb. apply match_iff_matchb in C.
                simpl. simpl in C. apply C.
          -- inv H0. destruct H1. injection H0. intros I1 I2. rewrite I2 in n. contradiction.
  }
Qed.

Lemma max_pref_matches : forall(code p x : String) (fsm : State),
  Some (p, x) = max_pref_fn code fsm
  -> exp_match p fsm.
Proof.
  induction code; intros p x fsm H.
  - assert (A0 : p = []).
    {
      apply max_pref_fn_splits in H. symmetry in H. destruct p.
      - reflexivity.
      - discriminate.
    }
    rewrite A0. simpl in H. destruct (accepting fsm) eqn:E0.
    + apply nullable_bridge. symmetry. apply E0.
    + discriminate.
  - simpl in H. destruct (max_pref_fn code (transition a fsm)) eqn:E0.
    + destruct p0. injection H. intros I1 I2. rewrite I2.
      symmetry in E0. apply IHcode in E0.
      apply match_iff_matchb. apply match_iff_matchb in E0. simpl. apply E0.
    + destruct (accepting (transition a fsm)) eqn:E1.
      * injection H. intros I1 I2. rewrite I2. apply match_iff_matchb.
        simpl. symmetry. apply E1.
      * destruct (accepting fsm) eqn:E2.
        -- injection H. intros I1 I2. rewrite I2. apply nullable_bridge. symmetry. apply E2.
        -- discriminate.
Qed.

Theorem max_pref_correct_Some : forall(code p : String) (fsm : State),
    max_pref code fsm p <-> exists(q : String), Some (p, q) = max_pref_fn code fsm.
Proof.
  induction code.
  {
    intros p fsm. split; intros H.
    - exists []. simpl. assert (A0 : p = []).
      {
        inv H. inv H1. destruct H0. destruct x.
        - rewrite nil_right in H. apply H.
        - destruct p.
          + reflexivity.
          + discriminate.
      }
      destruct (accepting fsm) eqn:E0.
      + rewrite A0. reflexivity.
      + inv H. apply nullable_bridge in H2. unfold accepting in E0.
        rewrite E0 in H2. discriminate.
    - destruct H. apply MP1.
      + apply max_pref_fn_splits in H. symmetry in H.
        apply pref_def. exists x. apply H.
      + apply max_pref_matches in H. apply H.
      + intros cand H0. inv H0. destruct H1.
        assert (A0 : cand = []).
        {
          destruct cand.
          - reflexivity.
          - discriminate.
        }
        assert (A1 : p = []).
        {
          simpl in H. destruct (accepting fsm).
          - injection H. intros I1 I2. apply I2.
          - discriminate.
        }
        rewrite A0. rewrite A1. left. omega.
  }
  {
    intros p fsm. split; intros H.
    - destruct p.
      + exists (a :: code). inv H. simpl.
        destruct (max_pref_fn code (transition a fsm)) eqn:E0.
        * destruct p. symmetry in E0.
          assert (Ae : exists q, Some (s, q) = max_pref_fn code (transition a fsm)).
          { exists s0. apply E0. }
          apply IHcode in Ae. inv Ae.
          assert (Ap : a :: s ++_= a :: code).
          { apply cons_prefix. split. reflexivity. apply H0. }
          apply H3 in Ap. destruct Ap.
          -- simpl in H. omega.
          -- exfalso. unfold not in H. destruct H.
             apply match_iff_matchb. apply match_iff_matchb in H4. simpl. apply H4.
        * assert (A0 : accepting (transition a fsm) = false).
          {
            destruct code.
            - simpl in E0. destruct (accepting (transition a fsm)).
              + discriminate.
              + reflexivity.
            - simpl in E0. destruct (max_pref_fn code (transition s (transition a fsm))).
              + destruct p. discriminate.
              + destruct (accepting (transition s (transition a fsm))).
                * discriminate.
                * destruct (accepting (transition a fsm)).
                  -- discriminate.
                  -- reflexivity.
          }
          rewrite A0. apply nullable_bridge in H2. unfold accepting. rewrite <- H2.
          reflexivity.
      + inv H. inv H1. destruct H0. injection H.
        intros I1 I2. clear H. exists x. subst s.
        assert (Ap : p ++_= code).
        { apply pref_def. exists x. apply I1. }
        simpl. destruct (max_pref_fn code (transition a fsm)) eqn:E0; symmetry in E0.
        * destruct p0.
          assert (Ae : exists q, Some (s, q) = max_pref_fn code (transition a fsm)).
          { exists s0. apply E0. }
          apply IHcode in Ae. inv Ae. inv H1. destruct H5. apply max_pref_fn_splits in E0.
          (* Want to show p = s *)
          assert (A0 : p ++_= p ++ x).
          { apply pref_def. exists x. reflexivity. }
          assert (A1 : a :: s ++_= a :: p ++ x).
          { apply pref_def. exists x0. rewrite <- H. reflexivity. }
          apply H3 in A1. apply H4 in A0.
          (* should follow that p and s0 are prefixes of the same length and thus equal *)
          assert (A0' : length p <= length s).
          {
            destruct A0.
            - apply H1.
            - exfalso. destruct H1. apply match_iff_matchb in H2. simpl in H2.
              apply match_iff_matchb. apply H2.
          }
          assert (A1' : length s <= length p).
          {
            destruct A1.
            - simpl in H1. omega.
            - exfalso. destruct H1. apply match_iff_matchb in H0.
              apply match_iff_matchb. simpl. apply H0.
          }
          assert (A : length p = length s).
          { omega. }
          assert (As : s ++_= p ++ x).
          { apply pref_def. exists x0. apply H. }
          apply eq_len_eq_pref with (x := p ++ x) in A.
          -- rewrite A. rewrite A in E0. apply app_inv_head in E0. rewrite E0. reflexivity.
          -- apply As.
          -- apply Ap.
        * apply max_pref_correct_None in E0. inv E0.
          assert (A0 : p = []).
          {
            assert (A1 : p ++_= p ++ x).
            { apply pref_def. exists x. reflexivity. }
            apply H1 in A1. unfold not in A1. destruct A1.
            apply match_iff_matchb. apply match_iff_matchb in H2. simpl in H2. subst. apply H2.
          }
          assert (A1 : accepting (transition a fsm) = true).
          { rewrite A0 in H2. apply match_iff_matchb in H2. simpl in H2. symmetry. apply H2. }
          rewrite A1. rewrite A0. reflexivity.
    - destruct H. apply MP1.
      + apply max_pref_fn_splits in H. apply pref_def. exists x. symmetry. apply H.
      + apply max_pref_matches in H. apply H.
      + intros cand Hpref. destruct p.
        * simpl in H.
          destruct (max_pref_fn code (transition a fsm)) eqn:E0.
          -- destruct p. discriminate.
          -- destruct (accepting (transition a fsm)) eqn:E1.
             ++ discriminate.
             ++ destruct (accepting fsm) eqn:E2.
                ** symmetry in E0. apply max_pref_correct_None in E0. inv E0. destruct cand.
                   { left. omega. }
                   { right. inv Hpref. destruct H0. injection H0. intros I1 I2.
                     unfold not. intros C. assert (A : cand ++_= code).
                     { apply pref_def. exists x0. apply I1. }
                     apply H1 in A. unfold not in A. destruct A.
                     apply match_iff_matchb in C. simpl in C. subst a.
                     apply match_iff_matchb. apply C.
                   }
                ** discriminate.
        * simpl in H.
          destruct (max_pref_fn code (transition a fsm)) eqn:E0; symmetry in E0.
          -- destruct p0. injection H. intros I1 I2 I3. 
             assert (Ae : exists q, Some (s0, q) = max_pref_fn code (transition a fsm)).
             { exists s1. apply E0. }
             apply IHcode in Ae. inv Ae. destruct cand.
             ++ left. simpl. omega.
             ++ inv Hpref. destruct H0. injection H0. intros I1 I2. subst s.
                assert (Apref : cand ++_= code).
                { apply pref_def. exists x. apply I1. }
                apply H3 in Apref. destruct Apref.
                ** left. simpl. omega.
                ** right. intros C. destruct H4. apply match_iff_matchb in C. simpl in C.
                   apply match_iff_matchb. apply C.
          -- apply max_pref_correct_None in E0. inv E0.
             assert (A0 : accepting (transition a fsm) = true).
             {
               destruct (accepting (transition a fsm)); destruct (accepting fsm);
                 try(reflexivity); try(discriminate).
             }
             assert (A1 : [] ++_= code).
             { apply pref_def. exists code. reflexivity. }
             apply H1 in A1. destruct A1. apply nullable_bridge. symmetry. apply A0.
  }
    
