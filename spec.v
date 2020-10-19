Require Import List.
Import ListNotations.

From VLG Require Import matcher.
From VLG Require Import coredefs.

Inductive is_prefix : String -> String -> Prop :=
| pref_def p s
           (H1 : exists q, p ++ q = s) :
    is_prefix p s.

Notation "p ++_= s" := (is_prefix p s) (at level 80).

Inductive re_no_max_pref : String -> regex -> Prop :=
| re_MP0 (s : String) (r : regex)
         (H1 : forall cand, cand ++_= s -> ~(exp_match cand r)) :
    re_no_max_pref s r.

Inductive re_max_pref : String -> regex -> String -> Prop :=
| re_MP1 (s p : String) (r : regex)
         (H1 : p ++_= s)
         (H2 : exp_match p r)
         (H3 : forall(cand : String),
             cand ++_= s
             -> ((length cand) <= (length p)) \/ ~(exp_match cand r)) :
    re_max_pref s r p.

Inductive no_max_pref : String -> State -> Prop :=
| MP0 (s : String) (fsm : State)
      (H1 : exists(r : regex), eq_models fsm r /\ re_no_max_pref s r) :
    no_max_pref s fsm.

Inductive max_pref : String -> State -> String -> Prop :=
| MP1 (s p : String) (fsm : State)
      (H1 : exists(r : regex), eq_models fsm r /\ re_max_pref s r p) :
    max_pref s fsm p.

(* a rule is at index 0 if it's the first element of the list.
   Otherwise a rule is at index n + 1 if it's at index n of the tail of the list *)
Inductive at_index : Rule -> nat -> list Rule -> Prop :=
| AI0 (ru h: Rule) (tl : list Rule)
      (Heq : ru = h) :
    at_index ru 0 (h :: tl)
| AI1 (ru h: Rule) (n : nat) (tl : list Rule)
      (IH : at_index ru n tl) :
    at_index ru (S n) (h :: tl).

(* n is the first index of a rule if no smaller index maps to that rule *)
Inductive least_index : Rule -> nat -> list Rule -> Prop :=
| LI1 (ru : Rule) (n : nat) (rus : list Rule)
      (Hat : at_index ru n rus)
      (Hnot : forall(n' : nat), n' < n -> ~(at_index ru n' rus)) :
    least_index ru n rus.

(* A rule is "earlier" than another if its first occurrence comes before
   the first occurence of the other rule *)
Inductive earlier_rule : Rule -> Rule -> list Rule -> Prop :=
| ERu1 (ru1 ru2 : Rule) (rus : list Rule)
       (H : forall(n1 n2 : nat),
           least_index ru1 n1 rus
           -> least_index ru2 n2 rus
           -> n1 < n2) :
    earlier_rule ru1 ru2 rus.

Inductive first_token : String -> (list Rule) -> Token -> Prop :=
(* l is Token.label, p is Token.value *)
| FT1 (code : String) (p : Prefix) (l : Label) (r : regex) (rus : list Rule)
      (Hnempt : p <> [])
      (Hex : In (l, r) rus)
      (Hmpref : re_max_pref code r p)
      (* We can't produce longer prefixes from other rules *)
      (Hout : forall(l' : String) (r' : regex) (p' : String),
          length p' > length p
          -> re_max_pref code r' p'
          -> ~(In (l',r') rus)
      )
      (* If we can produce the prefix in some other way,
           the rule used to do so most come later in the list *)
      (Hlater : forall(r' : regex) (l' : String),
          earlier_rule (l',r') (l, r) rus
          -> In (l', r') rus
          -> ~(re_max_pref code r' p)
      ) :
    first_token code rus (l, p).

(* This definition accounts for inputs that could not be entirely tokenized.
   The list of tokens must match some prefix and the unprocessed suffix
   must match s1 *)
Inductive tokenized (rus : list Rule) : String -> list Token -> String -> Prop :=
| Tkd0 (code : String)
       (H : forall(t : Token), first_token code rus t -> snd t = []) :
    (* If no tokens can be produced from the input,
       then the input is tokenized by the empty list
       of tokens and itself *)
    tokenized rus code [] code
| Tkd1 (p : Prefix) (s0 s1 : Suffix) (ts : list Token) (l : Label)
       (* the first token matches the input *)
       (H0 : first_token (p ++ s0 ++ s1) rus (l,p))
       (* The rest of the tokens match the rest of the input *)
       (IH : tokenized rus (s0 ++ s1) ts s1) :
    tokenized rus (p ++ s0 ++ s1) ((l, p) :: ts) s1.

Definition rules_is_function (rus : list Rule) :=
  forall l r r', In (l, r) rus
                 -> In (l, r') rus
                 -> r = r'.
