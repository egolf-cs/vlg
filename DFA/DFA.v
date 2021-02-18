Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From VLG Require Import ltac.
From VLG Require Import sigma.
From VLG Require Import matcher.

From VLG Require Import simdef.
From VLG Require Import simcorrect.

From VLG Require Import Table.
From VLG Require Import Table_spec.
From VLG Require Import Tablecorrect.

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

Fixpoint DFAtransition_list (bs : list Sigma) (dfa : DFA) : DFA :=
  match bs with
  | [] => dfa
  | c :: cs => DFAtransition_list cs (DFAtransition c dfa)
  end.

Definition DFAaccepting (dfa : DFA) : bool :=
  match dfa with
    (e, T, fins)
    => match find (fun x => re_sim e x) fins with
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

Lemma In_fin_nullable : forall es x,
    In x (fin_states es)
    -> nullable x = true.
Proof.
  induction es; intros.
  - contradiction.
  - simpl in H. destruct (nullable a) eqn:E.
    + simpl in H. destruct H.
      * subst; auto.
      * auto.
    + auto.
Qed.

Theorem DFAaccepting_nullable : forall es T e,
    DFAaccepting (e, T, fin_states es) = nullable e.
Proof.
  intros. unfold DFAaccepting. dm.
  apply find_some in E. destruct E.
  apply In_fin_nullable in H.
  apply re_sim_nullable in H0.
  symmetry in H. rewrite H0 in *; auto.
Qed.

Theorem transition_Table_correct : forall e e' T es,
  regex2dfa e = (e', T, es)
  -> derived T /\ (exists es', es = fin_states es') /\ e = e'.
Proof.
  intros. 
  unfold regex2dfa in *. injection H; intros.
  repeat(split); auto.
  - eapply derived_closure_all; eauto. apply emptyTable_derived.
  - eexists; eauto.
Qed.

Theorem transition_deriv : forall es es' e e' T T' a,
    derived T
    -> DFAtransition a (e, T, es) = (e', T', es')
    -> re_sim (derivative a e) e' = true
      /\ T = T' /\ es = es'.
Proof.
  intros. unfold derived in *. unfold DFAtransition in *. dm.
  - injection H0; intros; subst. clear H0.
    apply H in E. rewrite re_sim_symm. auto.
  - injection H0; intros; subst. inv H0.
    split; [apply re_sim_refl | split; auto].
Qed.

Lemma accepts_cons : forall z a dfa,
  DFAaccepts (a :: z) dfa
  = DFAaccepts z (DFAtransition a dfa).
Proof.
  auto.
Qed.

Lemma unfold_transition_list : forall bs a dfa,
  DFAtransition_list bs (DFAtransition a dfa)
  = DFAtransition_list (a :: bs) dfa.
Proof.
  auto.
Qed.
      
Lemma accepts_str_lst : forall z dfa,
    DFAaccepts z dfa = DFAaccepting (DFAtransition_list z dfa).
Proof.
  induction z; intros; auto.
  rewrite accepts_cons. rewrite <- unfold_transition_list.
  apply IHz.
Qed.
  
Theorem accepts_deriv : forall z es T e a,
    (forall (es : list regex) (T : Table) (e : regex),
        derived T -> DFAaccepts z (e, T, fin_states es) = exp_matchb z e)
    -> derived T
    -> DFAaccepts (a :: z) (e, T, fin_states es)
      = DFAaccepts z (derivative a e, T, fin_states es).
Proof.
  intros. rewrite accepts_cons. do 2 rewrite accepts_str_lst.
  unfold DFAtransition. repeat dm.
  do 2 rewrite <- accepts_str_lst.
  rewrite H; auto. rewrite H; auto.
  apply derived_get_some in E; auto.
  apply re_sim_equiv in E. unfold re_equiv in E.
  destruct (exp_matchb z r) eqn:E1.
  - symmetry in E1. rewrite match_iff_matchb in *. apply E. auto.
  - symmetry. rewrite false_not_true in *. intros C. destruct E1.
    symmetry. symmetry in C. rewrite match_iff_matchb in *. apply E. auto.
Qed.

Theorem accepts_matchb : forall z es T e,
    derived T
    -> DFAaccepts z (e, T, fin_states es)
      = exp_matchb z e.
Proof.
  induction z; intros.
  - simpl. dm. apply find_some in E; destruct E.
    apply In_fin_nullable in H0.
    apply re_sim_nullable in H1. rewrite H1. auto.
  - rewrite accepts_deriv; auto.
    rewrite der_matchb'; auto.
Qed.

Theorem accepts_match : forall z es T e,
    derived T ->
    (DFAaccepts z (e, T, fin_states es) = true <-> exp_match z e).
Proof.
  intros. rewrite accepts_matchb; auto.
  rewrite <- match_iff_matchb. split; symmetry; auto.
Qed.

Theorem r2d_accepts_match : forall z e,
    DFAaccepts z (regex2dfa e) = true <-> exp_match z e.
Proof.
  intros. destruct regex2dfa eqn:H0. destruct p. apply transition_Table_correct in H0.
  do 3 destruct H0. subst.
  apply accepts_match; auto.
Qed.
