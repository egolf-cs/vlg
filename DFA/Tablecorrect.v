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

Theorem emptyTable_derived : derived emptyTable.
Proof.
  unfold derived. intros. rewrite Table.correct_emptyTable in H. discriminate.
Qed.

Lemma unfold_filler : forall bs T e n,
    fill_Table_all T e bs (S n)
    =
    let
      fix fill_Table_ds (bs' : list Sigma) : Table :=
      match bs' with
      | [] => T
      | c :: cs =>
        let T1 := fill_Table_ds cs in
        let d := derivative c e in
        match get_sim T d with
        | Some e' => set_Table T1 e c e'
        | None =>
          let T2 := add_state T1 d in
          let T3 := set_Table T2 e c d in fill_Table_all T3 d bs n
        end
      end in
    fill_Table_ds bs.
Proof.
  auto.
Qed.

Lemma unfold_filler_ds : forall T T' e x xs n,
    let
      fix fill_Table_ds (bs' : list Sigma) : Table :=
      match bs' with
      | [] => T
      | c :: cs =>
        let T1 := fill_Table_ds cs in
        let d := derivative c e in
        match get_sim T d with
        | Some e' => set_Table T1 e c e'
        | None =>
          let T2 := add_state T1 d in
          let T3 := set_Table T2 e c d in fill_Table_all T3 d (x :: xs) n
        end
      end in
    T' = fill_Table_ds (x :: xs)
    ->
    (exists e' T0, get_sim T (derivative x e) = Some e'
           /\ T0 = (fill_Table_ds xs)
           /\ T' = set_Table T0 e x e')
    \/
    (exists T0, get_sim T (derivative x e) = None
           /\
           T0 = (fill_Table_ds xs)
           /\
           T' = fill_Table_all
                  (set_Table (add_state T0 (derivative x e)) e x
                           (derivative x e))
                  (derivative x e) (x :: xs) n).
Proof.
  intros. simpl in *. destruct (get_sim T (derivative x e)) eqn:E.
  - left. eexists; eauto.
  - right. eexists; eauto.
Qed.

Theorem derived_closure_set : forall T b e r,
  derived T
  -> re_sim r (derivative b e) = true
  -> derived (set_Table T e b r).
Proof.
  intros.
  (* 1. T' is derived before the set. 
     2. We know (derivative b e) and r are similar.
     3. The only entry in T' that changes is the (e, b) entry
     ---
     4. T' is still derived after the set.
   *)
  unfold derived. intros.
  (* If e = e0 and a = b, r = r0. Otherwise the entry was there before the set. *)
  (** may need a hypothesis about getting something that wasn't set **)
  destruct (regex_eq e e0) eqn:E; destruct (Sigma_dec a b).
  - apply regex_eq_correct in E. subst.
    rewrite Table.correct_Table in H1. injection H1; intros; subst.
    auto.
  - rewrite Table.moot_setTable in H1; auto.
  - rewrite Table.moot_setTable in H1; auto.
    assert(regex_eq e e0 <> true).
    { intros C. rewrite C in *. discriminate. }
    right. intros C. destruct H2. apply regex_eq_correct. auto.
  - rewrite Table.moot_setTable in H1; auto.
Qed.

Theorem derived_closure_add : forall T T' e,
  derived T
  -> T' = add_state T e
  -> derived T'.
Proof.
  unfold derived in *. intros.
  rewrite H0 in H1. rewrite <- Table.moot_add_state with (r:=e) in H1.
  apply H in H1. auto.
Qed.
  
Theorem derived_closure_ds' : forall bs T T' e n xs,
    (forall (cs : list Sigma) (e : regex) (T T' : Table),
        derived T -> T' = fill_Table_all T e cs n -> derived T')
    -> derived T
    ->
    let
      fix fill_Table_ds (bs' : list Sigma) : Table :=
      match bs' with
      | [] => T
      | c :: cs =>
        let T1 := fill_Table_ds cs in
        let d := derivative c e in
        match get_sim T d with
        | Some e' => set_Table T1 e c e'
        | None =>
          let T2 := add_state T1 d in
          let T3 := set_Table T2 e c d in fill_Table_all T3 d xs n
        end
      end in
    T' = fill_Table_ds bs
    -> derived T'.
Proof.
  intros.
  generalize dependent T.
  generalize dependent T'.
  generalize dependent e.
  generalize dependent xs.
  induction bs as [|b bs]; intros.
  - subst; auto.
  - simpl in H1. repeat dm.
    + assert(derived (fill_Table_ds bs)).
      {
        apply IHbs with (T:=T) (e:=e) (xs:=xs); auto.
      }
      apply get_sim_correct in E. destruct E.
      rewrite H1.
      apply derived_closure_set; auto.
      rewrite re_sim_symm. auto.
    + assert(derived (fill_Table_ds bs)).
      {
        apply IHbs with (T:=T) (e:=e) (xs:=xs); auto.
      }
      assert(derived (add_state (fill_Table_ds bs) (derivative b e))).
      {
        eapply derived_closure_add; eauto.
      }
      clear H2.
      assert(derived (set_Table
                        (add_state (fill_Table_ds bs) (derivative b e)) e b (derivative b e))).
      {
        eapply derived_closure_set; eauto.
        apply re_sim_refl.
      }
      eapply H; eauto.
Qed.
  
Theorem derived_closure_ds : forall bs T e n xs,
    (forall (cs : list Sigma) (e : regex) (T T' : Table),
        derived T -> T' = fill_Table_all T e cs n -> derived T')
    -> derived T
    ->
    let
      fix fill_Table_ds (bs' : list Sigma) : Table :=
      match bs' with
      | [] => T
      | c :: cs =>
        let T1 := fill_Table_ds cs in
        let d := derivative c e in
        match get_sim T d with
        | Some e' => set_Table T1 e c e'
        | None =>
          let T2 := add_state T1 d in
          let T3 := set_Table T2 e c d in fill_Table_all T3 d xs n
        end
      end in
    derived (fill_Table_ds bs).
Proof.
  intros. apply derived_closure_ds' with (bs:=bs) (T:=T) (e:=e) (n:=n) (xs:=xs); auto.
Qed.
  
  
Theorem derived_closure_all : forall n bs e T T',
    derived T
    -> T' = fill_Table_all T e bs n
    -> derived T'.
Proof.
  induction n; intros; try(simpl in H0; subst; auto; reflexivity).
  destruct bs as [|b bs].
  - simpl in H0. subst. auto.
  - apply unfold_filler_ds in H0. destruct H0.
    + destruct H0 as (e' & T0 & H0 & H1 & H2).
      assert(derived T0).
      {
        apply derived_closure_ds with (bs:=bs) (xs:= (b :: bs)) (e:=e) (n:=n) in H.
        subst. auto. apply IHn.
      }
      clear H1.
      subst. eapply derived_closure_set; eauto.
      apply Table.get_sim_correct in H0. destruct H0.
      rewrite re_sim_symm. auto.
    + destruct H0 as (T0 & H0 & H1 & H2).
      assert(derived T0).
      {
        apply derived_closure_ds with (bs:=bs) (xs:= (b :: bs)) (e:=e) (n:=n) in H.
        subst. auto. apply IHn.
      }
      clear H1.
      assert(derived (add_state T0 (derivative b e))).
      {
        eapply derived_closure_add; eauto.
      }
      assert(derived (set_Table (add_state T0 (derivative b e)) e b (derivative b e))).
      {
        eapply derived_closure_set; eauto. apply re_sim_refl.
      }
      eapply IHn; eauto.
Qed.

Lemma derived_get_some : forall T e a e',
    derived T
    -> get_Table T e a = Some e'
    -> re_sim e' (derivative a e) = true.
Proof.
  intros. unfold derived in *. apply H in H0. auto.
Qed.
