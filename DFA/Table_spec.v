Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From VLG Require Import ltac.
From VLG Require Import sigma.
From VLG Require Import matcher.

From VLG Require Import simdef.

From VLG Require Import Table.

Definition derived (T : Table) : Prop :=
  forall e a r, get_Table T e a = Some r -> re_sim r (derivative a e) = true.
