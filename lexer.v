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



Definition Label : Type := String.
Definition Prefix : Type := String.
Definition Suffix : Type := String.
Definition Rule : Type := Label * regex.
Definition Token : Type := Label * Prefix.
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
Definition init_state_inv (fsm : State) : regex := fsm.
Definition sRule : Type := Label * State.

Lemma invert_init_correct : forall(r : regex),
    init_state_inv (init_state r) = r.
Proof.
  intros r. unfold init_state. unfold init_state_inv. reflexivity.
Qed.


Fixpoint max_pref_fn (s : String) (state : State) : option (Prefix * Suffix):=
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

Lemma max_pref_fn_splits : forall code prefix suffix (fsm : State),
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

Lemma proper_suffix_shorter : forall code prefix suffix (fsm : State),
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
        
Definition extract_fsm_for_max (code : String) (sru : (Label * State)) :=
  match sru with
    (a, fsm) => (a, max_pref_fn code fsm)
  end.

Definition max_prefs (code : String) (erules : list (Label * State)) :=
    map (extract_fsm_for_max code) erules.

(* it looks like prefixes closest to the head are preffered *)
Definition longer_pref (apref1 apref2 : Label * (option (Prefix * Suffix)))
  : Label * (option (Prefix * Suffix)) :=
  match apref1, apref2 with
  | (_, None), (_, _) => apref2
  | (_, _), (_, None) => apref1
                          (* This is finding the min right now... *)
  | (_, Some (x, _)), (_, Some (y, _)) => if (length x) =? (length y)
                                         then apref1 else
                                           if (length x) <? (length y)
                                           then apref2 else apref1
  end.

Fixpoint max_of_prefs (mprefs : list (Label * (option (Prefix * Suffix))))
  : Label * option (Prefix * Suffix) :=
  match mprefs with
  | [] => ([], @None (String * String))
  | p :: ps => longer_pref p (max_of_prefs ps)
  end.

(* interesting that no induction was required here *)
Lemma max_first_or_rest : forall ys x y,
    x = max_of_prefs (y :: ys) -> x = y \/ x = max_of_prefs ys.
Proof.
  intros ys x y H. simpl in H. destruct y.
  destruct o; unfold longer_pref in H; destruct (max_of_prefs ys).  
  - destruct p. destruct o.
    + destruct p0. destruct (length p =? length p0).
      * left. apply H.
      * destruct (length p <? length p0).
        -- right. apply H.
        -- left. apply H.
    + left. apply H.
  - right. apply H.
Qed.
    
Program Fixpoint lex'
         (rules : list sRule)
         (code : String)
         {measure (length code)} : (list Token) * String :=
  let (* find all the maximal prefixes, associating them with a rule as we go *)
    mprefs := max_prefs code rules
  in
  let (* of these maximal prefixes, find the longest *)
    mpref := max_of_prefs mprefs
  in
  match mpref with
  | (_, None) => ([], code) (* Code cannot be processed further *)
  | (_, Some ([], _)) => ([], code) (* Code cannot be processed further *)
  | (label, Some (prefix, suffix)) =>
    match (lex' rules suffix) with
    | (lexemes, rest) => (((label, prefix) :: lexemes), rest)
    end
  end.
Next Obligation.
  assert (A0 : prefix <> []).
  {
    unfold not. intros C. rewrite C in H.
    specialize (H label). specialize (H suffix).
    contradiction.
  }
  assert (A2 : exists(fsm : State), Some (prefix, suffix) = max_pref_fn code fsm).
  { 
    induction rules.
    - simpl in Heq_mpref. discriminate.
    - simpl in Heq_mpref. apply max_first_or_rest in Heq_mpref. destruct Heq_mpref.
      + destruct a in H0. exists s. injection H0. intros I1 I2. apply I1.
      + apply IHrules.
        * destruct rules.
          -- simpl in H0. discriminate.
          -- apply H0.
  }
  destruct A2 as [fsm].
  apply proper_suffix_shorter with (suffix := suffix) (code := code) (fsm := fsm) in A0.
  - apply A0.
  - apply H0.
Qed.

Fixpoint lex'' 
         (rules : list sRule)
         (code : String)
         (Ha : Acc lt (length code))
         {struct Ha} : (list Token) * String.
  refine(
  let (* find all the maximal prefixes, associating them with a rule as we go *)
    mprefs := max_prefs code rules
  in
  let (* of these maximal prefixes, find the longest *)
    mpref := max_of_prefs mprefs
  in
  match mpref as mpref' return mpref = mpref' -> _ with
  | (_, None) => fun _ => ([], code) (* Code cannot be processed further *)
  | (_, Some ([], _)) => fun _ => ([], code) (* Code cannot be processed further *)
  | (label, Some (prefix, suffix)) => fun Heq =>
    match (lex'' rules suffix _) with
    | (lexemes, rest) => (((label, prefix) :: lexemes), rest)
    end
  end eq_refl).
  apply Acc_inv with (x := length code).
  - apply Ha.
  - assert (A0 : exists mp, mp = max_of_prefs (max_prefs code rules)).
    { exists mpref. auto. }
    destruct A0 as [mp].
    assert (A1 : mp = mpref).
    { auto. }
    rewrite <- A1 in Heq. rewrite H in Heq.
    clear A1 H mpref mprefs mp p o prefix Ha lex''.
    assert(A2 : exists(fsm : State), Some (s :: l, suffix) = max_pref_fn code fsm).
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

Lemma lex''_eq_body : forall rules code x,
    lex'' rules code = x
    -> (exists proof,
          (fun _ =>
          (let (* find all the maximal prefixes, associating them with a rule as we go *)
            mprefs := max_prefs code rules
          in
          let (* of these maximal prefixes, find the longest *)
            mpref := max_of_prefs mprefs
          in
          match mpref as mpref' return mpref = mpref' -> _ with
          | (_, None) => fun _ => ([], code) (* Code cannot be processed further *)
          | (_, Some ([], _)) => fun _ => ([], code) (* Code cannot be processed further *)
          | (label, Some (prefix, suffix)) =>
            fun Heq =>
              match (lex'' rules suffix (proof suffix)) with
              | (lexemes, rest) => (((label, prefix) :: lexemes), rest)
              end
          end eq_refl)) = x).
Proof.
  intros rules code.
Admitted.
     

(** Attempt to circumvent refine **)
(*
Lemma acc_prop_suffix : forall code rules label s l suffix,
  (mprefs :=  max_prefs code rules)
  -> (mpref := max_of_prefs mprefs)
  -> mpref = (label, Some (s :: l, suffix))
  -> Acc lt (length code)
  -> Acc lt (length suffix).
Admitted.

Fixpoint lex''' 
         (rules : list sRule)
         (code : String)
         (Ha : Acc lt (length code))
         {struct Ha} : (list Token) * String :=
  let (* find all the maximal prefixes, associating them with a rule as we go *)
    mprefs := max_prefs code rules
  in
  let (* of these maximal prefixes, find the longest *)
    mpref := max_of_prefs mprefs
  in
  match mpref as mpref' return mpref = mpref' -> _ with
  | (_, None) => fun _ => ([], code) (* Code cannot be processed further *)
  | (_, Some ([], _)) => fun _ => ([], code) (* Code cannot be processed further *)
  | (label, Some (prefix, suffix)) =>
    fun Heq =>
      match (lex'' rules suffix (acc_prop_suffix ...))
      with
      | (lexemes, rest) => (((label, prefix) :: lexemes), rest)
    end
  end eq_refl).
*)
    
Definition init_srule (rule : Rule) : sRule :=
  match rule with
  | (label, re) => (label, init_state re)
  end.

Definition lex (rules : list Rule) (code : String) :=
  let
    srules := map init_srule rules
  in
  lex'' srules code.

(* destruct a match in a hypothesis *)
Ltac dmh := match goal with | H : context[match ?x with | _ => _ end] |- _ => destruct x eqn:?E end.
(* destruct a match in the goal *)
Ltac dmg := match goal with | |- context[match ?x with | _ => _ end] => destruct x eqn:?E end.
Ltac dm := (first [dmh | dmg]); auto.

Theorem lex'_eq_body : forall(rules : list sRule) (code : String),
    lex' rules code =
    let (* find all the maximal prefixes, associating them with a rule as we go *)
      mprefs := max_prefs code rules
    in
    let (* of these maximal prefixes, find the longest *)
      mpref := max_of_prefs mprefs
    in
    match mpref with
    | (_, None) => ([], code) (* Code cannot be processed further *)
    | (_, Some ([], _)) => ([], code) (* Code cannot be processed further *)
    | (label, Some (prefix, suffix)) =>
      match (lex' rules suffix) with
      | (lexemes, rest) => (((label, prefix) :: lexemes), rest)
      end
    end.
Proof.
  intros rules code.
  unfold lex'. unfold lex'_func.
  rewrite Wf.fix_sub_eq; auto.
  - simpl; repeat dm.
  - intros. destruct x. simpl. repeat dm. admit.
  Admitted.
  
  
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

Lemma nil_is_prefix : forall(xs : String),
    [] ++_= xs.
Proof.
  intros xs. apply pref_def. exists xs. reflexivity.
Qed.

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

Lemma self_prefix : forall(p : String), p ++_= p.
Proof.
  intros p. apply pref_def. exists []. apply nil_right.
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

Inductive eq_models : State -> regex -> Prop :=
| SReq (fsm : State) (r : regex)
       (H1 : forall(s : String), true = accepts s fsm <-> exp_match s r) :
    eq_models fsm r.

Lemma accepts_matches : forall(s : String) (fsm : State),
    true = accepts s fsm <-> exp_match s (init_state_inv fsm).
Proof.
  intros s fsm. apply match_iff_matchb.
Qed.

Lemma inv_eq_model : forall(fsm : State),
    eq_models fsm (init_state_inv fsm).
Proof.
  intros fsm. apply SReq. intros s. apply match_iff_matchb.
Qed.

Lemma accepts_nil: forall(fsm : State),
    accepting fsm = accepts [] fsm.
Proof.
  intros fsm. reflexivity.
Qed.

Inductive re_no_max_pref : String -> regex -> Prop :=
| re_MP0 (s : String) (r : regex)
      (H1 : forall cand, cand ++_= s -> ~(exp_match cand r)) :
    re_no_max_pref s r.

Inductive re_max_pref : String -> regex -> String -> Prop :=
| re_MP1 (s p : String) (r : regex)
         (H1 : p ++_= s)
         (H2 : exp_match p r)
         (H3 : forall(cand : String),
             cand ++_= s
             -> ((length cand) <= (length p)) \/ ~(exp_match cand r)) :
    re_max_pref s r p.

Inductive no_max_pref : String -> State -> Prop :=
| MP0 (s : String) (fsm : State)
      (H1 : exists(r : regex), eq_models fsm r /\ re_no_max_pref s r) : 
    no_max_pref s fsm.

Inductive max_pref : String -> State -> String -> Prop :=
| MP1 (s p : String) (fsm : State)
      (H1 : exists(r : regex), eq_models fsm r /\ re_max_pref s r p) : 
    max_pref s fsm p.

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

Theorem re_max_pref_correct__None : forall(code : String) (fsm : State),
    re_no_max_pref code (init_state_inv fsm)
    <-> None = max_pref_fn code fsm.
Proof.
  intros code fsm. split.
  {
    generalize dependent fsm; induction code; intros fsm H.
    - simpl. inv H. specialize (H1 []). assert (A : [] ++_= []).
      { apply nil_is_prefix. }
      apply H1 in A. clear H1. destruct (accepting fsm) eqn:E.
      + exfalso. unfold not in A. destruct A. apply nullable_bridge.
        symmetry. unfold accepting in E. apply E.
      + reflexivity.
    - specialize (IHcode (transition a fsm)). inv H.
      assert (A0 : re_no_max_pref code (init_state_inv (transition a fsm))).
      {
        apply re_MP0.
        - intros cand H. specialize (H1 (a :: cand)).
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
        { apply nil_is_prefix. }
        apply H1 in A3. apply false_not_true. unfold not. intros C.
        unfold not in A3. destruct A3. apply nullable_bridge. unfold accepting in C.
        symmetry. apply C.
      } 
      rewrite <- A0. rewrite A1. rewrite A2. reflexivity.
  }
  {
    generalize dependent fsm; induction code; intros fsm H.
    - apply re_MP0.
      + intros cand H0. simpl in H.
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
        unfold not. intros C. rewrite A1 in C. rewrite accepts_nil in A0.
        apply accepts_matches in C. rewrite A0 in C. discriminate.
    - specialize (IHcode (transition a fsm)).
      apply re_MP0.
      intros cand H0. simpl in H. destruct (max_pref_fn code (transition a fsm)).
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
        * intros C. rewrite accepts_nil in A1. apply accepts_matches in C.
          rewrite A1 in C. discriminate.
        * destruct (Sigma_dec a s).
          -- rewrite <- e. destruct cand.
             ++ unfold not. intros C. apply accepts_matches in C. simpl in C.
                unfold accepting in A0. unfold transition in A0.
                rewrite A0 in C. discriminate.
             ++ assert (A2 : re_no_max_pref code (init_state_inv (transition a fsm))).
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

Theorem re_max_pref_correct__Some : forall(code p : String) (fsm : State),
    re_max_pref code (init_state_inv fsm) p
    <-> exists(q : String), Some (p, q) = max_pref_fn code fsm.
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
      + inv H. rewrite accepts_nil in E0. apply accepts_matches in H2.
        rewrite E0 in H2. discriminate.
    - destruct H. apply re_MP1.
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
          assert (Ae : exists q, Some (p, q) = max_pref_fn code (transition a fsm)).
          { exists s. apply E0. }
          apply IHcode in Ae. inv Ae.
          assert (Ap : a :: p ++_= a :: code).
          { apply cons_prefix. split. reflexivity. apply H0. }
          apply H3 in Ap. destruct Ap.
          -- simpl in H. omega.
          -- exfalso. unfold not in H. destruct H.
             apply accepts_matches. simpl. apply accepts_matches in H4. apply H4.
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
          rewrite A0. apply accepts_matches in H2. rewrite <- accepts_nil in H2.
          rewrite <- H2. reflexivity.
      + inv H. inv H1. destruct H0. injection H.
        intros I1 I2. clear H. exists x. subst s.
        assert (Ap : p ++_= code).
        { apply pref_def. exists x. apply I1. }
        simpl. destruct (max_pref_fn code (transition a fsm)) eqn:E0; symmetry in E0.
        * destruct p0.
          assert (Ae : exists q, Some (p0, q) = max_pref_fn code (transition a fsm)).
          { exists s. apply E0. }
          apply IHcode in Ae. inv Ae. inv H1. destruct H5. apply max_pref_fn_splits in E0.
          (* Want to show p = p0 *)
          assert (A0 : p ++_= p ++ x).
          { apply pref_def. exists x. reflexivity. }
          assert (A1 : a :: p0 ++_= a :: p ++ x).
          { apply pref_def. exists x0. rewrite <- H. reflexivity. }
          apply H3 in A1. apply H4 in A0.
          (* should follow that p and p0 are prefixes of the same length and thus equal *)
          assert (A0' : length p <= length p0).
          {
            destruct A0.
            - apply H1.
            - exfalso. destruct H1. apply accepts_matches in H2.
              apply accepts_matches. simpl in H2. apply H2.
          }
          assert (A1' : length p0 <= length p).
          {
            destruct A1.
            - simpl in H1. omega.
            - exfalso. destruct H1. apply accepts_matches in H0.
              apply accepts_matches. simpl. apply H0.
          }
          assert (A : length p = length p0).
          { omega. }
          assert (As : p0 ++_= p ++ x).
          { apply pref_def. exists x0. apply H. }
          apply eq_len_eq_pref with (x := p ++ x) in A.
          -- rewrite A. rewrite A in E0. apply app_inv_head in E0. rewrite E0. reflexivity.
          -- apply As.
          -- apply Ap.
        * apply re_max_pref_correct__None in E0. inv E0.
          assert (A0 : p = []).
          {
            assert (A1 : p ++_= p ++ x).
            { apply pref_def. exists x. reflexivity. }
            apply H1 in A1. unfold not in A1. destruct A1. apply accepts_matches.
            apply accepts_matches in H2. simpl in H2. apply H2.
          }
          assert (A1 : accepting (transition a fsm) = true).
          { rewrite A0 in H2. apply accepts_matches in H2. simpl in H2. symmetry. apply H2. }
          rewrite A1. rewrite A0. reflexivity.
    - destruct H. apply re_MP1.
      + apply max_pref_fn_splits in H. apply pref_def. exists x. symmetry. apply H.
      + apply max_pref_matches in H. apply H.
      + intros cand Hpref. destruct p.
        * simpl in H.
          destruct (max_pref_fn code (transition a fsm)) eqn:E0.
          -- destruct p. discriminate.
          -- destruct (accepting (transition a fsm)) eqn:E1.
             ++ discriminate.
             ++ destruct (accepting fsm) eqn:E2.
                ** symmetry in E0. apply re_max_pref_correct__None in E0. inv E0. destruct cand.
                   { left. omega. }
                   {
                     right. inv Hpref. destruct H0. injection H0. intros I1 I2.
                     unfold not. intros C. assert (A : cand ++_= code).
                     { apply pref_def. exists x0. apply I1. }
                     apply H1 in A. unfold not in A. destruct A.
                     apply accepts_matches in C. simpl in C. subst a.
                     apply accepts_matches. apply C.
                   }
                ** discriminate.
        * simpl in H.
          destruct (max_pref_fn code (transition a fsm)) eqn:E0; symmetry in E0.
          -- destruct p0. injection H. intros I1 I2 I3. 
             assert (Ae : exists q, Some (p0, q) = max_pref_fn code (transition a fsm)).
             { exists s0. apply E0. }
             apply IHcode in Ae. inv Ae. destruct cand.
             ++ left. simpl. omega.
             ++ inv Hpref. destruct H0. injection H0. intros I1 I2. subst s.
                assert (Apref : cand ++_= code).
                { apply pref_def. exists x. apply I1. }
                apply H3 in Apref. destruct Apref.
                ** left. simpl. omega.
                ** right. intros C. destruct H4. apply accepts_matches in C. simpl in C.
                   apply accepts_matches. apply C.
          -- apply re_max_pref_correct__None in E0. inv E0.
             assert (A0 : accepting (transition a fsm) = true).
             {
               destruct (accepting (transition a fsm)); destruct (accepting fsm);
                 try(reflexivity); try(discriminate).
             }
             assert (A1 : [] ++_= code).
             { apply nil_is_prefix. }
             apply H1 in A1. destruct A1. apply accepts_matches. rewrite <- accepts_nil.
             symmetry. apply A0.
  }
Qed.

Theorem max_pref_correct__None : forall(code : String) (fsm : State),
    no_max_pref code fsm
    <-> None = max_pref_fn code fsm.
Proof.
  intros code fsm. split; intros H.
  - inv H. destruct H1 as [r]. destruct H. assert(H' := H0). inv H0.
    (* show that r and (init_state_inv fsm) are equivalent regex's. 
       show that equivalent regex's can be substituted into H'.
       Then apply previous correctness definition.
     *)
    assert(Aeq := inv_eq_model fsm).
    assert(A0 : forall(s : String), exp_match s r <-> exp_match s (init_state_inv fsm)).
    {
      inv H. inv Aeq. intros s.
      specialize (H2 s). specialize (H0 s).
      split.
      - intros H. apply H0 in H. apply H2 in H. apply H.
      - intros H. apply H0. apply H2. apply H.
    }
    assert(A1 : re_no_max_pref code (init_state_inv fsm)).
    {
      apply re_MP0.
      - intros cand Hpref. specialize (H1 cand). apply H1 in Hpref.
        intros C. destruct Hpref. apply A0 in C. apply C.
    }
    apply re_max_pref_correct__None in A1. apply A1.
  - apply re_max_pref_correct__None in H. apply MP0. exists (init_state_inv fsm). split.
    + apply inv_eq_model.
    + apply H.
Qed.
    
Theorem max_pref_correct__Some : forall(code p : String) (fsm : State),
    max_pref code fsm p
    <-> exists(q : String), Some (p, q) = max_pref_fn code fsm.
Proof.
  intros code p fsm. split; intros H.
  - inv H. destruct H1 as [r]. destruct H. assert(H' := H0). inv H0.
    (* show that r and (init_state_inv fsm) are equivalent regex's. 
       show that equivalent regex's can be substituted into H'.
       Then apply previous correctness definition.
     *)
    assert(Aeq := inv_eq_model fsm).
    assert(A0 : forall(s : String), exp_match s r <-> exp_match s (init_state_inv fsm)).
    {
      inv H. inv Aeq. intros s.
      specialize (H4 s). specialize (H0 s).
      split.
      - intros H. apply H0 in H. apply H4 in H. apply H.
      - intros H. apply H0. apply H4. apply H.
    }
    assert(A1 : re_max_pref code (init_state_inv fsm) p).
    {
      apply re_MP1.
      - apply H1.
      - apply A0. apply H2.
      - intros cand Hpref. apply H3 in Hpref. destruct Hpref.
        + left. apply H0.
        + right. intros C. destruct H. apply A0 in C. contradiction.
    }
    apply re_max_pref_correct__Some in A1. apply A1.
  - apply re_max_pref_correct__Some in H. apply MP1. exists (init_state_inv fsm). split.
    + apply inv_eq_model.
    + apply H.
Qed.

(* Sam's zoom message:

 List.nth_error : list A -> nat -> option A 
at_index r n rs == ... 
List.nth_error rs n = Some r 
least_index r n rs == ... 
List.nth_error rs n = Some r /\... 
forall n', List.nth_error rs n' = Some r -> n < n' *)

(* a rule is at index 0 if it's the first element of the list.
   Otherwise a rule is at index n + 1 if it's at index n of the tail of the list *)
Inductive at_index : Rule -> nat -> list Rule -> Prop :=
| AI0 (ru h: Rule) (tl : list Rule)
      (Heq : ru = h) :
    at_index ru 0 (h :: tl)
| AI1 (ru h: Rule) (n : nat) (tl : list Rule)
      (IH : at_index ru n tl) :
    at_index ru (n + 1) (h :: tl).

(* n is the first index of a rule if no smaller index maps to that rule *)
Inductive least_index : Rule -> nat -> list Rule -> Prop :=
| LI1 (ru : Rule) (n : nat) (rus : list Rule)
      (Hat : at_index ru n rus)
      (Hnot : forall(n' : nat), n' < n -> ~(at_index ru n' rus)) :
    least_index ru n rus.

(* A rule is "earlier" than another if its first occurrence comes before
   the first occurence of the other rule *)
Inductive earlier_rule : Rule -> Rule -> list Rule -> Prop :=
| ERu1 (ru1 ru2 : Rule) (rus : list Rule)
       (H : forall(n1 n2 : nat),
           least_index ru1 n1 rus
           -> least_index ru2 n2 rus
           -> n1 < n2) :
    earlier_rule ru1 ru2 rus.

(* Given an explicit witness, r:regex, we define the first token *)
Inductive first_token_expl : String -> regex -> (list Rule) -> Token -> Prop :=
(* l is Token.label, p is Token.value *)
| FTE1 (code : String) (p : Prefix) (l : Label) (r : regex) (rus : list Rule)
        (Hex : In (l, r) rus)
        (Hmpref : re_max_pref code r p)
        (* We can't produce longer prefixes from other rules *)
        (* disjunction might be used to combine Hout and Hlater *)
        (Hout : forall(l' : String) (r' : regex) (p' : String),
            (* (In (l',r') rus)
            -> re_max_pref code r' p'
            -> length p' <= length p *)
            length p' > length p
            -> re_max_pref code r' p'
            -> ~(In (l',r') rus)
        )
        (* If we can produce the prefix in some other way,
           the rule used to do so most come later in the list *)
        (Hlater : forall(l' : String) (r' : regex) (p' : String),
            length p' = length p
            -> re_max_pref code r' p'
            -> In (l',r') rus
            -> earlier_rule (l, r) (l', r') rus
        ) :
    first_token_expl code r rus (l, p).

(* Now we say that if such a witness exists, the Token is the first token *)
Inductive first_token : list Rule -> String -> Token -> Prop :=
| FT1 (code : String) (p : Prefix) (l : Label) (rus : list Rule) (r : regex)
      (Hex : first_token_expl code r rus (l, p)) :
    first_token rus code (l, p).

(* This definition accounts for inputs that could not be entirely tokenized.
   The list of tokens must match some prefix and the unprocessed suffix
   must match s1 *)
Inductive tokenized (rus : list Rule) : String -> list Token -> String -> Prop :=
| Tkd0 (code : String)
      (H : forall(t : Token), first_token rus code t -> snd t = []) :
    (* If no tokens can be produced from the input,
       then the input is tokenized by the empty list 
       of tokens and itself *)
    tokenized rus code [] code
| Tkd1 (p : Prefix) (s0 s1 : Suffix) (t : Token) (ts : list Token)
      (* the first token matches the input *)
      (H0 : first_token rus (p ++ s0 ++ s1) t)
      (* the first token matches the relevant prefix *)
      (H1 : snd t = p)
      (* The rest of the tokens match the rest of the input *)
      (IH : tokenized rus (s0 ++ s1) ts s1) :
    tokenized rus (p ++ s0 ++ s1) (t :: ts) s1.

Lemma no_tokens_suffix_self : forall rus code rest,
    lex rus code = (fun _ => ([], rest)) -> code = rest.
Proof.
  intros rus code rest H.
  unfold lex in H. apply lex''_eq_body in H. destruct H.
  destruct (max_prefs code (map init_srule rus)); simpl in H.
  - injection H. intros I1. apply I1.
  - destruct (longer_pref p (max_of_prefs l)). destruct o.
    + destruct p0. destruct p0.
      * injection H. intros I1. apply I1.
      * destruct ( lex' (map init_srule rus) s). discriminate.
    + injection H. intros I1. apply I1.
Qed.

Lemma pref_not_no_pref : forall code p r,
  re_max_pref code r p
  -> ~(re_no_max_pref code r).
Proof.
  intros code p r H C. inv H. inv C.
  apply H0 in H1. contradiction.
Qed.

Lemma max_pref_fn_Some_or_None : forall code fsm,
  (exists p q, Some (p, q) = max_pref_fn code fsm)
  \/ None = max_pref_fn code fsm.
Proof.
  intros code fsm. destruct (max_pref_fn code fsm).
  - left. destruct p. exists p. exists s. reflexivity.
  - right. reflexivity.
Qed.

Lemma re_pref_or_no_pref : forall code r,
    (exists p, re_max_pref code r p) \/ re_no_max_pref code r.
Proof.
  intros code r. assert(L := max_pref_fn_Some_or_None).
  specialize (L code). specialize (L (init_state r)). destruct L.
  - left. destruct H as [p]. apply re_max_pref_correct__Some in H.
    exists p. rewrite invert_init_correct in H. apply H.
  - right. apply re_max_pref_correct__None in H.
    rewrite invert_init_correct in H. apply H.
Qed.


Lemma part_around_in : forall rus (ru : Rule),
    In ru rus -> (exists rus1 rus2, rus = rus1 ++ (ru :: rus2)).
Proof.
  induction rus; intros ru Hin. contradiction.
  simpl in Hin. destruct Hin.
  - exists []. exists rus. rewrite H. reflexivity.
  - apply IHrus in H. destruct H as [rus1]. destruct H as [rus2]. rewrite H.
    exists (a :: rus1). exists rus2. reflexivity.
Qed.

Ltac inj_all :=
  match goal with
  | H:context [ (_, Some(_, _)) = (_, Some(_, _)) ] |- _ => injection H; intros; subst; clear H
  end.

Ltac eqb_eq_all :=
  match goal with
  | H:context [ (_ =? _) = _ ] |- _ => try(rewrite false_not_true in H); rewrite Nat.eqb_eq in H
  end.

Ltac ltb_lt_all :=
  match goal with
  | H:context [ (_ <? _) = _ ] |- _ => try(rewrite false_not_true in H); rewrite Nat.ltb_lt in H
  end.

(* Ah so this is what proof automation can do... *)
Lemma lgr_pref_assoc : forall a b c,
    longer_pref (longer_pref a b) c = longer_pref a (longer_pref b c).
Proof.
  intros a b c. unfold longer_pref.
  repeat dm; repeat inj_all; subst; repeat eqb_eq_all; repeat ltb_lt_all;
    try(discriminate);
    try(omega);
    try(auto).
Qed.

Lemma mpref_app_dist : forall ps1 ps2,
    max_of_prefs (ps1 ++ ps2) = longer_pref (max_of_prefs ps1) (max_of_prefs ps2).
Proof.
  induction ps1; intros ps2.
  - simpl. destruct (max_of_prefs ps2). reflexivity.
  - simpl. rewrite IHps1. symmetry. apply lgr_pref_assoc.
Qed.

Lemma mpref_cons : forall ps p,
    max_of_prefs (p :: ps) = longer_pref p (max_of_prefs ps).
Proof.
  intros ps p. simpl. reflexivity.
Qed.
                                             
Lemma nil_mpref_nil_or_no_pref : forall rus code s l l1 r,
  max_of_prefs (max_prefs code (map init_srule rus)) = (l1, Some ([], s))
  -> In (l, r) rus
  -> re_max_pref code r [] \/ re_no_max_pref code r.
Proof.
  intros rus code s l l1 r Hmax Hin. assert(L := re_pref_or_no_pref code r).
  destruct L.
  - destruct H. destruct x.
    + left. apply H.
    (* This was a fun one *)
    + exfalso.
      replace (r) with (init_state_inv (init_state r)) in H.
      2: { apply invert_init_correct. }
      apply re_max_pref_correct__Some in H. destruct H as [q]. symmetry in H.
      assert(L := (part_around_in rus (l, r)) Hin).
      destruct L as (rus1 & rus2 & L). subst rus. clear Hin.
      rewrite map_app in Hmax. rewrite map_cons in Hmax. simpl in Hmax.
      unfold max_prefs in Hmax. rewrite map_app in Hmax. rewrite map_cons in Hmax. simpl in Hmax.
      rewrite H in Hmax. rewrite mpref_app_dist in Hmax. rewrite mpref_cons in Hmax.
      simpl in Hmax. unfold longer_pref in Hmax.
      (* 32 subgoals, 7 subproofs ! *)
      repeat dmh; subst; 
        try (discriminate);
        try(injection Hmax; intros I1 I2 I3; subst p0;
            destruct p2; [discriminate | simpl in E5; discriminate]);
        try(injection E2; intros; subst; discriminate);
        try(rewrite Hmax in E1; discriminate).
      * injection E2; intros; injection Hmax; intros; subst;
        rewrite E11 in E5; simpl in E5; discriminate.
      * injection E2; intros; injection Hmax; intros; subst;
          destruct (length p0); simpl in E6; rewrite Nat.ltb_lt in E6; omega.
      * rewrite Hmax in E1. injection E1; intros; subst. simpl in E7; discriminate.
  - right. apply H.
Qed.

Lemma no_mpref_no_pref : forall rus code l l1 r,
  max_of_prefs (max_prefs code (map init_srule rus)) = (l1, None)
  -> In (l, r) rus
  -> re_no_max_pref code r.
Proof.
  intros rus code l l1 r Hmax Hin. assert(L := re_pref_or_no_pref code r).
  destruct L.
  - exfalso.
    destruct H. replace (r) with (init_state_inv (init_state r)) in H.
    2: { apply invert_init_correct. }
    apply re_max_pref_correct__Some in H. destruct H as [q]. symmetry in H.
    assert(L := (part_around_in rus (l, r)) Hin).
    destruct L as (rus1 & rus2 & L). subst rus. clear Hin.
    rewrite map_app in Hmax. rewrite map_cons in Hmax. simpl in Hmax.
    unfold max_prefs in Hmax. rewrite map_app in Hmax. rewrite map_cons in Hmax. simpl in Hmax.
    rewrite H in Hmax. rewrite mpref_app_dist in Hmax. rewrite mpref_cons in Hmax.
    simpl in Hmax. unfold longer_pref in Hmax.
    repeat dmh; repeat inj_all; subst;
      try(discriminate);
      try(rewrite Hmax in E1; discriminate).
  - apply H.
Qed.

Lemma no_tokens_no_pref : forall code rest rus l r,
  lex rus code = ([], rest)
  -> In (l, r) rus
  -> re_max_pref code r [] \/ re_no_max_pref code r.
Proof.
  intros code rest rus l r Hlex Hin.
  unfold lex in Hlex. rewrite lex'_eq_body in Hlex.
  destruct (max_prefs code (map init_srule rus)) eqn:E0; simpl in Hlex.
  - assert(C : rus = []).
    { destruct rus. reflexivity. simpl in E0. discriminate. }
    rewrite C in Hin. contradiction.
  - destruct (longer_pref p (max_of_prefs l0)) eqn:E1.
    replace (longer_pref p (max_of_prefs l0))
      with (max_of_prefs (p :: l0)) in E1. 2: { reflexivity. }
    rewrite <- E0 in E1.
    destruct o.
    + destruct p0. destruct p0.
      * apply nil_mpref_nil_or_no_pref with (l := l) (r := r) in E1.
        -- apply E1.
        -- apply Hin.
      * destruct (lex' (map init_srule rus) s). discriminate.
    + right. apply no_mpref_no_pref with (l := l) (r := r) in E1.
      * apply E1.
      * apply Hin.
Qed.

Lemma max_pref_unique : forall code r p p',
  re_max_pref code r p
  -> re_max_pref code r p'
  -> p = p'.
Proof.
  intros code r p p' Hp Hp'.
  inv Hp. inv Hp'.
  assert(Hp := H1). assert(Hp' := H0).
  apply H5 in H1. apply H3 in H0. clear H3 H5.
  assert(A : length p <= length p' /\ length p' <= length p).
  { split; [destruct H1 | destruct H0]; try (apply H); try (contradiction). }
  assert (Aeq : length p' = length p).
  { omega. }
  apply eq_len_eq_pref with (x := code) in Aeq.
  apply Aeq. apply Hp. apply Hp'.
Qed.

Lemma tokens_head : forall code rest rus a ts,
  lex rus code = (a :: ts, rest)
  -> first_token rus code a.
Admitted.

Lemma tokens_tail : forall ts a code rest rus, 
    lex rus code = (a :: ts, rest)
    -> exists(p code' : String),
      p ++ code' ++ rest = code
      /\ snd a = p
      /\ lex rus (code' ++ rest) = (ts, rest).
Admitted.

Theorem lex_tokenizes : forall ts code rest rus,
    lex rus code = (ts, rest) -> tokenized rus code ts rest.
Proof.
  induction ts; intros code rest rus H.
  {
    assert (H' := H).
    apply no_tokens_suffix_self in H'. rewrite H'. apply Tkd0. subst.
    intros t Hfst. inv Hfst. simpl. inv Hex.
    apply no_tokens_no_pref with (l := l) (r := r) in H. 2: { apply Hex0. }
    destruct H.
    - apply max_pref_unique with (p := p) in H. 2: { apply Hmpref. }
      apply H.
    - apply pref_not_no_pref in Hmpref. contradiction.    
  }
  {
    assert (H' := H).
    apply tokens_head in H. apply tokens_tail in H'.
    destruct H' as (p & code' & H'). destruct H' as (Heq & Hval & IP).
    apply IHts in IP. subst code. apply Tkd1.
    - apply H.
    - apply Hval.
    - apply IP.
  }
Qed.
           
             
              
            
      
