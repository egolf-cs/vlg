Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.

Definition Sigma := ascii.
Parameter SigmaEnum : list Sigma.
Hypothesis SigmaEnum_correct : forall a, In a SigmaEnum.
