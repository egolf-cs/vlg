Require Import List.
Import ListNotations.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

From VLG Require Import lexer.
From VLG Require Import matcher.
From VLG Require Import sigma.
From VLG Require Import coredefs.

Definition ru1 : Rule := ([A], Star(Char A)).
Definition ru2 : Rule := ([A;B], App (Char A) (Char B)).
Definition ru3 : Rule := ([B;A], App (Char B) (Char A)).
Definition rus : list Rule := [ru1;ru2;ru3].
Definition code : String := [A;A;A;B;A;B;B;A].

Extraction "evaluation/instance.ml" lex rus code.
