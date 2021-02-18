Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From VLG Require Import ltac.
From VLG Require Import sigma.
From VLG Require Import matcher.
From VLG Require Import simdef.
From VLG Require Import simcorrect.


Parameter Table : Type.
Parameter emptyTable : Table.
(*The first regex is for indexing, the second is the content of the cell*)
Parameter set_Table : Table -> regex -> Sigma -> regex -> Table.
Parameter get_Table : Table -> regex -> Sigma -> option (regex).

Hypothesis correct_Table : forall T e a r, get_Table (set_Table T e a r) e a = Some (r).
Hypothesis moot_setTable : forall T e0 e a b r,
    a <> b
    \/ e <> e0
    -> get_Table (set_Table T e b r) e0 a = get_Table T e0 a.
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
Hypothesis moot_add_state : forall T e a r,
    get_Table T e a = get_Table (add_state T r) e a.
(* might need a hypothesis about not being in states *)

Fixpoint get_sim' (es : list regex) (e : regex) : option regex :=
  match es with
  | [] => None
  | h :: t => if re_sim e h then Some h else get_sim' t e
  end.
  
Definition get_sim (T : Table) (e : regex) : option regex :=
  get_sim' (get_states T) e.

(** uniqueness issues? *)
Theorem get_sim'_correct : forall T e e',
    get_sim T e = Some e' -> In e' (get_states T) /\ re_sim e e' = true.
Proof.
  intros T. induction (get_states T) eqn:E.
  - intros. unfold get_sim in H. rewrite E in H. simpl in H. discriminate.
  - (* need a more general IH *)
Admitted.
                               
Theorem get_sim_correct : forall T e e',
    get_sim T e = Some e' -> In e' (get_states T) /\ re_sim e e' = true.
Proof.
  intros. unfold get_sim in *. apply get_sim'_correct; auto.
Qed.

(* This version should be entirely valid, upto parameters and hypotheses.
   The problem is that it doesn't address final states.
   Final states can be addressed in the DFA module.
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
