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

Fixpoint max_pref_fn (s : String) (r : regex) : option String :=
  match s with
  (* in a DFA approach, nullable r would instead check if the DFA is in an accept state *)
  | [] => if nullable r then Some [] else None
  | a :: s' =>
    let
      (* in a DFA approach, (derivative a r) would instead be a state transition *)
      r' := derivative a r in
    let
      mpxs := max_pref_fn s' r' in
    
    match mpxs with
    | None => if (nullable r') then Some [a] else None
    | Some s'' => Some (a :: s'')
    end
  end.

(* Maybe it would be better to build the suffix while also building the prefix? *)
Fixpoint get_suffix (p : String) (s : String) :=
  match p, s with
  | [], _ => Some s (* p consumed, the rest is suffix *)
  | _, [] => None (* p longer than s *)
  | b::bs, c::cs => if Sigma_dec b c then get_suffix bs cs
                 else None (* if characters don't match up point-wise, p is not a prefix *)
  end.

(* couldn't find this in the list library? *)
Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(* 
   This function will accept a list of pairs and a string.
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
Program Fixpoint lex (rules : list Rule) (code : String) {measure (length code)} : list eToken :=
  match code with
  | [] => []
  | _ =>
    let (* find all the maximal prefixes, associating them with a rule as we go *)
      mprefs := map (fun ru => match ru with (a, re) => ((a, re), max_pref_fn code re) end) rules
    in
    let (* of these maximal prefixes, find the longest *)
      mpref := fold (fun apref1 apref2 =>
                       match apref1, apref2 with
                       | (_, None), (_, _) => apref2
                       | (_, _), (_, None) => apref1
                       | (_, Some x), (_, Some y) => if (length y) <? (length x)
                                                    then apref2 else apref1
                       end
                    ) mprefs (([], EmptySet), None)
    in
    let (* get the associated suffix -- might be better to build this while building the prefix? *)
      msuff := match mpref with
                    | (_, None) => None (* This state suggests malformed code *)
                    | (_, Some x) => get_suffix x code
               end
    in
    match mpref, msuff with
    | (_, None), _ => [] (* This state suggests malformed code *)
    | _, None => [] (* This state suggests malformed code *)
    | (ru, Some prefix), Some suffix => (ru, prefix, suffix) :: (lex rules suffix)
    end
      
  end.
                 
  
  
