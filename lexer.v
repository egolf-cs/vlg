Require Import Ascii.
Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.Program.Wf.

From VLG Require Import regex.

Definition Sigma := regex.Sigma.
Definition Sigma_dec := regex.Sigma_dec.
Definition String := regex.String.

Definition Rule : Type := String * regex.
Definition Token : Type := String * String.
Definition eToken : Type := Rule * String * String.
Definition eLexemes : Type := list eToken.
(* 
   The lexer will accept a list of pairs and a string.
   Each element in this list of pairs will contain a regex and its corresponding label/action.

   The function will return a list of triples.
   Each element in this list of triples will be of the form ((a, re), pre, suff).
   The tokens can be extracted as (a, pref), where a is the label/action and 
     pre is the labeled word.

   The additional elements in the triple might be helpful for correctness.

   0. An error will be thrown <-> the code could not be lexed entirely according to the rules
   In all cases where an error is not thrown:
   1. exp_match pref re
   2. the concatention of all pre is equal to code
   3. If suff = x ++ y, then pre ++ x does not match any of the regular expressions from rules
 *)

(*********************************************
*
*
*   Alternative formulation, more modular.
*
*
*********************************************)
Definition State : Type := regex.
Definition transition : Sigma -> State -> State := derivative.
Definition accepting : State -> bool:= nullable.
Definition init_state (r : regex) : State := r.
Definition absorbing_state := EmptySet.
(* in eRule, the State would be the initial state of the machine after converting from regex *)
Definition eRule : Type := String * regex * State.
Definition eeToken : Type := eRule * String * String.
Definition eeLexemes : Type := list eeToken.

Fixpoint max_pref_fn (s : String) (state : State) : option (String * String):=
  match s with
  (* in a regex approach, accepting := nullable *)
  | [] => if accepting state then Some ([],[]) else None
  | a :: s' =>
    let
      (* in a regex approach, transition := derivative *)
      state' := transition a state in
    let
      mpxs := max_pref_fn s' state' in
    
    match mpxs with
    | None => if (accepting state') then Some ([a], s') else None
    | Some (p, s'') => Some (a :: p, s'')
    end
  end.

Program Fixpoint lex (rules : list Rule) (code : String) {measure (length code)} : option (list eeToken) :=
  match code with
  | [] => Some []
  | _ =>
    let
      erules := map (fun ru => match ru with
                              (a,re) => (a, re, init_state re)
                            end) rules
    in
    let (* find all the maximal prefixes, associating them with a rule as we go *)
      mprefs := map (fun eru => match eru with
                               (a, re, fsm) => (Some (a, re, fsm), max_pref_fn code fsm)
                             end) erules
    in Some [] end.
    let (* of these maximal prefixes, find the longest *)
      mpref := (*fold_left (fun apref1 apref2 =>
                       match apref1, apref2 with
                       | (_, None), (_, _) => apref2
                       | (_, _), (_, None) => apref1
                       | (_, Some (x, _)), (_, Some (y, _)) => if (length y) <? (length x)
                                                    then apref2 else apref1
                       end
                         ) mprefs*) (None, None)
    in [] end.
    match mpref with
    | (_, None) => None (* This state suggests malformed code *)
    | (None, _) => None (* This state shouldn't be reachable *)
    | (Some eru, Some (prefix, suffix)) => match (lex rules suffix) with
                                     | None => None
                                     | Some lexemes =>
                                       Some ( (eru, prefix, suffix) :: lexemes )
                                     end
    end
      
  end.
                 
  
  
