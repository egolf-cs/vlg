Require Import List.
Import ListNotations.

Inductive Sigma :=
| A
| B.

Compute [A;B;A].
