Require Import List.
Import ListNotations.

Require Import Nat.

Require Import Ascii.
Require Import String.
Open Scope string_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

From VLG Require Import lexer.
From VLG Require Import matcher.
From VLG Require Import sigma.
From VLG Require Import coredefs.

(*** Some ascii helpers ***)
Fixpoint toS (s : string) : String
  := match s with
     | EmptyString => nil
     | String.String ch s => cons ch (list_ascii_of_string s)
     end.

Fixpoint range' (n : nat) : (list nat) :=
  match n with
  | 0 => []
  | S n' => (range' n') ++ [n']
  end.

Fixpoint range (n1 n2 : nat) : (list nat) := map (plus n1) (range' (n2 - n1 + 1)).

(*** Some regex helpers ***)
Definition Plus (r : regex) : regex := App r (Star r).

Fixpoint IterUnion (rs : list regex) :=
match rs with
| [] => EmptySet
| h::t => Union h (IterUnion t)
end.

Fixpoint IterApp (rs : list regex) :=
match rs with
| [] => EmptyStr
| h::t => App h (IterApp t)
end.

(* r? *)
Definition Optional (r : regex) := Union EmptyStr r.

(**)


(*** White Space ***)
(* [ \t\n\r] *)
Definition chars_ws := map Char (map ascii_of_nat [9;10;13;32]).
Definition ru_ws : Rule := (toS "WS", Plus (IterUnion chars_ws)).
(**)

(*** Numbers ***)
(* [0-9] *)
Definition ascii_digit := range 48 57.
Definition chars_digit := map Char (map ascii_of_nat ascii_digit).
Definition regex_digit := IterUnion chars_digit.

(* [1-9], nz = non-zero *)
Definition ascii_nz_digit := range 49 57.
Definition chars_nz_digit := map Char (map ascii_of_nat ascii_nz_digit).
Definition regex_nz_digit := IterUnion chars_nz_digit.

(* "fragment INT" *)
Definition regex_zero := Char (ascii_of_nat 48).
Definition regex_nzero := App regex_nz_digit (Star regex_digit).
Definition regex_int := Union regex_zero regex_nzero.

(* '-'? *)
Definition regex_sign := Char (ascii_of_nat 45).
Definition regex_sign_option := Optional regex_sign.
(* ('.' [0-9] +)? *)
Definition regex_dec_point := Char (ascii_of_nat 46).
Definition regex_dec := App regex_dec_point (Plus regex_digit).
Definition regex_dec_option := Optional regex_dec.
(* fragment EXP : [Ee] [+\-]? INT *)
Definition regex_Ee := Union (Char (ascii_of_nat 69)) (Char (ascii_of_nat 101)).
Definition regex_pm := Union (Char (ascii_of_nat 43)) (Char (ascii_of_nat 45)).
Definition regex_pm_option := Optional regex_pm.
Definition regex_exp := IterApp [regex_Ee;regex_pm_option;regex_int].
Definition regex_exp_option := Optional regex_exp.

(* NUMBER : '-'? INT ('.' [0-9] +)? EXP? *)
Definition regex_number := IterApp [regex_sign_option;regex_int;regex_dec_option;regex_exp_option].
Definition ru_number := (toS "NUMBER", regex_number).
(**)

(*** STRING ***)
Definition ascii_lower := range 97 122.
Definition chars_lower := map Char (map ascii_of_nat ascii_lower).
Definition regex_lower := IterUnion chars_lower.
Definition ascii_upper := range 65 90.
Definition chars_upper := map Char (map ascii_of_nat ascii_upper).
Definition regex_upper := IterUnion chars_upper.
(* not sure what to include for punctuation, but here's almost all of it. *)
(* Maybe too much, and no consideration for escaping characters. *)
(* In theory this is meant to support unicode... *)
Definition ascii_punc : (list nat) := [32;33] ++ (range 35 47) ++ (range 58 64) ++ (range 91 96) ++ (range 123 126).
Definition chars_punc := map Char (map ascii_of_nat ascii_punc).
Definition regex_punc := IterUnion chars_punc.
Definition regex_char := IterUnion [regex_lower;regex_upper;regex_digit;regex_punc].
Definition regex_par := Char (ascii_of_nat 34).
(* ru_string *)
Definition regex_string := IterApp [regex_par;(Star regex_char);regex_par].
Definition ru_string := (toS "STRING", regex_string).
(**)

(*** keywords ***)
Definition regex_true := IterApp (map Char (toS "true")).
Definition ru_true := (toS "TRUE", regex_true).
Definition regex_false := IterApp (map Char (toS "false")).
Definition ru_false := (toS "FALSE", regex_false).
Definition regex_null := IterApp (map Char (toS "null")).
Definition ru_null := (toS "NULL", regex_null).

(*** brack, brace, colon, comma ***)
Definition regex_colon := IterApp (map Char (toS ":")).
Definition ru_colon := (toS "COLON", regex_colon).
Definition regex_comma := IterApp (map Char (toS ",")).
Definition ru_comma := (toS "COMMA", regex_comma).
Definition regex_lbrack := IterApp (map Char (toS "[")).
Definition ru_lbrack := (toS "LEFT_BRACKET", regex_lbrack).
Definition regex_rbrack := IterApp (map Char (toS "]")).
Definition ru_rbrack := (toS "RIGHT_BRACKET", regex_rbrack).
Definition regex_lbrace := IterApp (map Char (toS "{")).
Definition ru_lbrace := (toS "LEFT_BRACE", regex_lbrace).
Definition regex_rbrace := IterApp (map Char (toS "}")).
Definition ru_rbrace := (toS "RIGHT_BRACE", regex_rbrace).


(*** Compile rules and export ***)
Definition rus : list Rule := [ru_ws;ru_number;ru_string;ru_true;ru_false;ru_null;ru_colon;ru_comma;ru_lbrack;ru_rbrack;ru_lbrace;ru_rbrace].
Extraction "evaluation/instance.ml" lex rus.
