From VLG Require Import matcher.

Notation "e1 = e2 " := (regex_eq e1 e2) (at level 70).
Notation "a ∂ r" := (derivative a r) (at level 75, right associativity).
Notation ε := EmptyStr.
Notation "[[ a ]]" := (Char a) (at level 75).
Notation "e *" := (Star e) (at level 75).
Notation "e1 @ e2" := (App e1 e2) (at level 75).
Notation "e1 # e2" := (Union e1 e2) (at level 75).
