Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From VLG Require Import ltac.
From VLG Require Import sigma.
From VLG Require Import matcher.

Parameter Table : Type.
Parameter emptyTable : Table.
(*The first regex is for indexing, the second is the content of the cell*)
Parameter set_Table : Table -> regex -> Sigma -> regex -> Table.
Parameter get_Table : Table -> regex -> Sigma -> option (regex).

Hypothesis correct_Table : forall T e a r, get_Table (set_Table T e a r) e a = Some (r).
(* might need a hypothesis about get_Table = None *)
Hypothesis correct_emptyTable : forall e a, get_Table emptyTable e a = None.


(* This function doesn't take derivatives with respect to every character *)
Fixpoint fill_Table_one (T : Table) (e : regex) (a : Sigma) (fuel : nat) : Table :=
  match fuel with
  | 0 => T
  | S n =>
    let
      d := derivative a e
    in
    fill_Table_one (set_Table T e a d) d a n
  end.

(* This version doesn't update the table, but does take all the derivatives *)
Fixpoint fill_Table_all' (T : Table) (es : list regex) (bs : list Sigma) (fuel : nat) : Table :=
  match fuel with
  | 0 => T
  | S n =>
    let
      dss := map (fun a => map (fun e => (derivative a e)) es) bs
    in
    match dss with
    | [] => T
    | ds :: dss' =>
      let
        T' := fill_Table_all' T (concat dss') bs n
      in
      fill_Table_all' T' ds bs n
    end
  end.

(* This version takes all the derivatives and updates the table,
   but it doesn't do checks for similarity *)
Fixpoint fill_Table_all'' (T : Table) (e : regex) (bs : list Sigma) (fuel : nat) : Table :=
  match fuel with
  | 0 => T
  | S n =>
    let
      fix fill_Table_ds (bs' : list Sigma) :=
      match bs' with
      | [] => T
      | c :: cs =>
        let
          T' := fill_Table_ds cs in
        let
          d := (derivative c e) in
        fill_Table_all'' (set_Table T' e c d) d bs n
      end
    in
    fill_Table_ds bs
  end.

Parameter add_state : Table -> regex -> Table.
Parameter get_states : Table -> list regex.
Hypothesis empty_states : get_states emptyTable = [].
Hypothesis correct_states : forall T r, In r (get_states (add_state T r)).
(* might need a hypothesis about not being in states *)

Parameter re_sim : regex -> regex -> bool.
Parameter get_sim : Table -> regex -> option regex.
(* There are probably uniqueness issues with this hypothesis *)
Hypothesis get_sim_correct : forall T e e',
    get_sim T e = Some e' <-> In e' (get_states T) /\ re_sim e e' = true.

(* This version should be entirely valid, upto parameters and hypotheses.
   The problem is that it doesn't address final states.
*)
Fixpoint fill_Table_all (T : Table) (e : regex) (bs : list Sigma) (fuel : nat) : Table :=
  match fuel with
  | 0 => T
  | S n =>
    let
      (* We need a helper function to apply fill_Table_all to each derivative of e *)
      fix fill_Table_ds (bs' : list Sigma) :=
      match bs' with
      | [] => T
      | c :: cs =>
        let
          (* fill the table with respect to the tail *)
          T1 := fill_Table_ds cs in
        let
          (* now we'll do it with respect to c *)
          d := (derivative c e) in
        match get_sim T d with
        | None =>
          let
            (* we didn't find a similar regex, we need to add d *)
            T2 := add_state T1 d in
          let
            (* we also need to transition from regex e to regex d on symbol c *)
            T3 := set_Table T2 e c d in
          (* finally we need to fill up the table with respect to d *)
          fill_Table_all T3 d bs n
        | Some e' =>
          (* In this case, we found a regex that has already been added to the table *)
          (* Anytime we add a regex, we immediately call fill_Table_all for it *)
          (* Therefore, we don't need to call fill_Table_all again *)
          (* Instead, we transition from e to e' when we see c *)
          set_Table T1 e c e'
        end
      end
    in
    fill_Table_ds bs
  end.

Fixpoint regex_depth (e : regex) : nat :=
  match e with
  | EmptySet
  | EmptyStr
  | Char _ => 0
  | App e1 e2
  | Union e1 e2 =>
    let
      d1 := regex_depth e1 in
    let
      d2 := regex_depth e2 in
    if leb d2 d1 then d1 + 1 else d2 + 1
  | Star e0 => (regex_depth e0) + 1
  end.
                        

Fixpoint fin_states (es : list regex) :=
  match es with
  | [] => []
  | h :: t =>
    let t' := fin_states t in
    if nullable h
    then h :: t'
    else t'
  end.

Definition DFA : Type := regex * Table * list regex.
Definition defDFA : DFA := (EmptySet, emptyTable, []).

Definition DFAtransition (a : Sigma) (dfa : DFA) : DFA :=
  match dfa with
    (e, T, fins)
    => match get_Table T e a with
      | Some e' => (e', T, fins)
      | None => (derivative a e, T, fins)
      end
  end.

Definition DFAaccepting (dfa : DFA) : bool :=
  match dfa with
    (e, T, fins)
    => match find (fun x => regex_eq e x) fins with
      | None => nullable e
      | Some _ => true
      end
  end.

Fixpoint DFAaccepts (z : String) (dfa : DFA) : bool :=
  match z with
  | [] => DFAaccepting dfa
  | x :: xs => DFAaccepts xs (DFAtransition x dfa)
  end.

Definition regex2dfa (e : regex) : DFA :=
  let
    T := fill_Table_all emptyTable e SigmaEnum (regex_depth e)
  in
  let
    es := get_states T
  in
  (e, T, fin_states es).
  
Definition dfa2regex (dfa : DFA) : regex :=
  match dfa with (e, _, _) => e end.

(** lemmas that belong somewhere else **)


(* Works for type A in general, but need dec_eq for A *)
Lemma in_split_first_regex : forall (l : list regex) (x : regex),
    In x l -> (exists l1 l2, l = l1 ++ x :: l2 /\ not(In x l1)).
Proof.
  induction l; intros.
  - contradiction.
  - destruct (regex_dec a x).
    + subst. exists []. exists l. auto.
    + destruct H.
      * contradiction.
      * apply IHl in H. destruct H as (l1 & l2 & Heq & Hnin).
        exists (a :: l1). exists l2. subst. split; auto. intros C. destruct C; contradiction.
Qed.
      
                                                                     
Lemma null_app_dist : forall e1 e2,
    nullable (App e1 e2) = andb (nullable e1) (nullable e2).
Proof.
  intros. simpl.
  destruct (nullable e2); destruct (nullable e1); auto; discriminate.
Qed.

Lemma null_union_dist : forall e1 e2,
    nullable (Union e1 e2) = orb (nullable e1) (nullable e2).
Proof.
  intros. simpl.
  destruct (nullable e2); destruct (nullable e1); auto; discriminate.
Qed.

(** Table lemmas **)

Lemma In_fin_app : forall xs1 xs2 x,
    In x (fin_states (xs1 ++ xs2))
    -> In x (fin_states xs1) \/ In x (fin_states xs2).
Proof.
  induction xs1; intros; auto.
  simpl in H. dm.
  - simpl in H. destruct H.
    + subst. left. simpl. rewrite E. simpl. left. auto.
    + apply IHxs1 in H. destruct H.
      * left. simpl. dm. simpl. right. auto.
      * right. auto.
  - apply IHxs1 in H. destruct H.
    + left. simpl. dm. discriminate.
    + auto.
Qed.

Lemma In_fin_In_states : forall xs x,
    In x (fin_states xs)
    -> In x xs.
Proof.
  induction xs; intros. contradiction.
  simpl in H. dm; simpl in *; try(destruct H); auto.
Qed.
  
Lemma In_fin_nullable : forall e n x,
    In x (fin_states (get_states (fill_Table_all emptyTable e SigmaEnum n)))
    -> nullable x = true.
Proof.
  intros.
  assert(L := In_fin_In_states (get_states (fill_Table_all emptyTable e SigmaEnum n)) x H).
  assert(A : exists xs1 xs2, xs1 ++ (x :: xs2) = get_states (fill_Table_all emptyTable e SigmaEnum n)
                        /\ not (In x xs1)).
  {
    apply in_split_first_regex in L. destruct L as (l1 & l2 & H0 & H2).
    eexists; eauto.
  }
  destruct A as (xs1 & xs2 & H0 & H1). rewrite <- H0 in *. clear L H0.
  apply In_fin_app in H. destruct H.
  - apply In_fin_In_states in H. contradiction.
  - clear H1 xs1. induction xs2.
    + simpl in H. dm.
    + simpl in H. repeat dm; simpl in *; repeat dm;
      destruct H; try(subst; rewrite E1 in E0; discriminate).
      apply IHxs2 in H. discriminate.
Qed.
    
Lemma gen_find_nullable : forall e r n,
    find (fun x : regex => regex_eq e x)
         (fin_states (get_states (fill_Table_all emptyTable e SigmaEnum n))) = 
    Some r
    -> nullable e = true.
Proof.
  intros. apply find_some in H. destruct H. apply In_fin_nullable in H.
  apply regex_eq_correct in H0. subst. auto.
Qed.

(* app *)
Lemma find_Table_app : forall e1 e2 r states,
    find
      (fun x : regex =>
         match x with
         | App x2 y2 => (regex_eq e1 x2 && regex_eq e2 y2)%bool
         | _ => false
         end) states =
    Some r
    -> exists x1 x2, r = App x1 x2.
Proof.
  intros. destruct r; try(apply find_some in H; destruct H; discriminate).
  eexists; eauto.
Qed.

Lemma app_find_nullable : forall e1 e2 r n,
    find
      (fun x : regex =>
         match x with
         | App x2 y2 => (regex_eq e1 x2 && regex_eq e2 y2)%bool
         | _ => false
         end) (fin_states (get_states (fill_Table_all emptyTable (App e1 e2) SigmaEnum n))) =
    Some r
    -> nullable e1 = true /\ nullable e2 = true.
Proof.
  intros.
  assert(L := H). apply find_Table_app in L. destruct L as [x1 [x2 L]]. subst.
  apply find_some in H. destruct H. apply In_fin_nullable in H. rewrite null_app_dist in H.
  apply andb_prop in H. destruct H.
  apply andb_prop in H0. destruct H0.
  apply regex_eq_correct in H0. apply regex_eq_correct in H2. subst.
  split; auto.
Qed.
(* * * *)
(* Union *)
Lemma find_Table_U : forall e1 e2 r states,
    find
      (fun x : regex =>
         match x with
         | Union x2 y2 => (regex_eq e1 x2 && regex_eq e2 y2)%bool
         | _ => false
         end) states =
    Some r
    -> exists x1 x2, r = Union x1 x2.
Proof.
  intros. destruct r; try(apply find_some in H; destruct H; discriminate).
  eexists; eauto.
Qed.

Lemma U_find_nullable : forall e1 e2 r n,
    find
      (fun x : regex =>
         match x with
         | Union x2 y2 => (regex_eq e1 x2 && regex_eq e2 y2)%bool
         | _ => false
         end) (fin_states (get_states (fill_Table_all emptyTable (Union e1 e2) SigmaEnum n))) =
    Some r
    -> nullable e1 = true \/ nullable e2 = true.
Proof.
  intros.
  assert(L := H). apply find_Table_U in L. destruct L as [x1 [x2 L]]. subst.
  apply find_some in H. destruct H. apply In_fin_nullable in H. rewrite null_union_dist in H.
  apply andb_prop in H0. destruct H0.
  apply regex_eq_correct in H0. apply regex_eq_correct in H1. subst.
  apply Bool.orb_prop; auto.
Qed.
(* * * *)

(** **)

                                                                                   
(** nil lemmas **)

Lemma acc_app_dist : forall e1 e2,
  DFAaccepting (regex2dfa (App e1 e2)) =
  (DFAaccepting (regex2dfa e1) && DFAaccepting (regex2dfa e2))%bool.
Proof.
  intros. simpl.
  destruct (nullable e1) eqn:nE1; destruct (nullable e2) eqn:nE2;
    destruct (regex_depth e1) eqn:dE1; destruct (regex_depth e2) eqn:dE2; repeat dm;
      try(simpl in *; rewrite empty_states in *; simpl in *; discriminate);
      try(apply app_find_nullable in E; destruct E; rewrite nE1 in *;
          rewrite nE2 in *; discriminate);
      try(apply gen_find_nullable in E3; rewrite nE2 in *; discriminate);
      try(apply gen_find_nullable in E2; rewrite nE1 in *; discriminate).
Qed.
    
Lemma acc_union_dist : forall e1 e2,
  DFAaccepting (regex2dfa (Union e1 e2)) =
  (DFAaccepting (regex2dfa e1) || DFAaccepting (regex2dfa e2))%bool.
Proof.
  intros. simpl.
  destruct (nullable e1) eqn:nE1; destruct (nullable e2) eqn:nE2;
    destruct (regex_depth e1) eqn:dE1; destruct (regex_depth e2) eqn:dE2; repeat dm;
      try(apply U_find_nullable in E; destruct E;
          try(rewrite nE1 in *); try(rewrite nE2 in *); discriminate);
              try(apply gen_find_nullable in E1; rewrite nE1 in *; discriminate);
              try(apply gen_find_nullable in E2; rewrite nE2 in *; discriminate).
              Qed.

Lemma accepts_nil_dfa : forall dfa,
    DFAaccepts [] dfa = DFAaccepting dfa.
Proof.
  auto.
Qed.

Lemma accepting_nullable_dfa : forall e,
    DFAaccepting (regex2dfa e) = nullable e.
Proof.
  induction e;
    try(simpl; rewrite empty_states; reflexivity).
  - rewrite null_app_dist. rewrite <- IHe1. rewrite <- IHe2. apply acc_app_dist.
  - rewrite null_union_dist. rewrite <- IHe1. rewrite <- IHe2. apply acc_union_dist.
  - simpl. repeat dm.
Qed.
(**)

(** cons lemmas **)

Definition eq_DFAs (dfa1 dfa2 : DFA) : Prop :=
  forall z, DFAaccepts z dfa1 = DFAaccepts z dfa2.

Fixpoint DFAtransition_list (bs : list Sigma) (dfa : DFA) : DFA :=
  match bs with
  | [] => dfa
  | c :: cs => DFAtransition c (DFAtransition_list cs dfa)
  end.


Fixpoint derivative_list (bs : list Sigma) (e : regex) : regex :=
  match bs with
  | [] => e
  | c :: cs => derivative c (derivative_list cs e)
  end.

Lemma deriv_transitions_nil : forall bs e,
    DFAaccepting (DFAtransition_list bs (regex2dfa e))
    = DFAaccepting (regex2dfa (derivative_list bs e)).
Proof.
Admitted.

Lemma deriv_transition_nil : forall e a,
    DFAaccepting (DFAtransition a (regex2dfa e))
    = DFAaccepting (regex2dfa (derivative a e)).
Proof.
Admitted.

Lemma accepts_transitions : forall bs z b dfa,
  DFAaccepts (b :: z) (DFAtransition_list bs dfa)
  = DFAaccepts z (DFAtransition_list (b :: bs) dfa).
Proof.
  induction bs; destruct z; intros; auto.
Qed.

Lemma accepts_transition : forall z a dfa,
    DFAaccepts (a :: z) dfa
    = DFAaccepts z (DFAtransition a dfa).
Proof.
  intros.
  assert(L := accepts_transitions [] z a dfa).
  unfold DFAtransition_list in *. auto.
Qed.
  
Lemma deriv_transition_eq : forall e a,
    eq_DFAs (DFAtransition a (regex2dfa e)) (regex2dfa (derivative a e)).
Proof.
  intros. unfold eq_DFAs. intros.
  generalize dependent a.
  generalize dependent e.
  induction z; intros.
  - unfold DFAaccepts. apply deriv_transition_nil.
  - repeat rewrite accepts_transition.
    rewrite IHz.
Qed.

Lemma accepts_cons_dfa : forall z e a,
    DFAaccepts (a :: z) (regex2dfa e) = DFAaccepts z (regex2dfa (derivative a e)).
Proof.
  intros. apply deriv_transition_eq.
Qed.

(**)

(** main correctness proofs **)

Lemma regex2dfa_correct' : forall z e,
    exp_matchb z e = DFAaccepts z (regex2dfa e).
Proof.
  induction z; intros.
  - rewrite accepts_nil_dfa. rewrite accepting_nullable_dfa. auto.
  - rewrite accepts_cons_dfa. apply IHz.
Qed.
  
Theorem regex2dfa_correct : forall z e,
    exp_match z e <-> DFAaccepts z (regex2dfa e) = true.
Proof.
  intros. rewrite <- regex2dfa_correct' with (e:=e).
  split; intros; try(symmetry); try(symmetry in H); apply match_iff_matchb; auto.
Qed.
