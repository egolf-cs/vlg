Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.

(* Borrowed these from another paper, actually about regex derivatives *)
Variable Sigma : Type.
Variable a : Sigma.
Variable b : Sigma.
Variable c : Sigma.
Variable Sigma_dec : forall (c c': Sigma), {c = c'} + {c <> c'}.
Axiom Sigma_dec_refl : forall(a : Sigma), true = if Sigma_dec a a then true else false.

(* Didn't bother with Intersection and Complement yet *)
Inductive reg_exp : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : Sigma)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Fixpoint re_exact (r s : reg_exp) :=
  match r, s with
  | EmptySet, EmptySet => true
  | EmptySet, EmptyStr=> false
  | EmptySet, Char _ => false

  | EmptyStr, EmptySet => false
  | EmptyStr, EmptyStr => true
  | EmptyStr, Char _ => false

  | Char _, EmptySet => false
  | Char _, EmptyStr => false
  | Char a, Char b => if Sigma_dec a b then true else false

  | Union r1 r2, Union s1 s2 => andb (re_exact r1 s1) (re_exact r2 s2)
  | App r1 r2, App s1 s2 => andb (re_exact r1 s1) (re_exact r2 s2)
  | Star r', Star s' => re_exact r' s'

  | _, _ => false
  end.

Definition simplify (r : reg_exp) : reg_exp :=
  match r with
  | App EmptySet r' => EmptySet
  | App r' EmptySet => EmptySet
  | App EmptyStr r' => r'
  | App r' EmptyStr => r'
  | Union EmptySet r' => r'
  | Union r1 r2 => if re_exact r1 r2 then r1 else r
  | Star (Star r') => Star r'
  | Star EmptyStr => EmptyStr
  | Star EmptySet => EmptySet
  | _ => r
  end.

(* check associativity/commutativity properties on one side *)
Definition similar_left (r s : reg_exp) : bool :=
  if re_exact r s then true else
    
    match r, s with
    
    (* App is associative *)
    | App (App r1 r2) r3, App s1 (App s2 s3) => andb (andb (re_exact r1 s1) (re_exact r2 s2)) (re_exact r3 s3)

    (* Union *)
                                     (* Union is commutative *)          
    | Union r1 t3, Union u1 s2 => if andb (re_exact r1 s2) (re_exact t3 u1) then true else
                                   match r1, s2 with
                                     (* Union is associative *)
                                   | Union t1 t2, Union u2 u3 => andb (andb (re_exact t1 u1) (re_exact t2 u2)) (re_exact t3 u3)
                                   | _, _ => re_exact r s
                                   end

    | _, _ => re_exact r s
    end.

Theorem same_choice : forall(b : bool), true = if b then true else true.
Proof.
  intros b. destruct b; reflexivity.
Qed.

Theorem or_true_true : forall(b : bool), true = orb b true.
Proof.
  intros b. destruct b; simpl; reflexivity.
Qed.

(* check assoc/comm on both sides, after applying simplification rules *)
Definition similar (r' s' : reg_exp) : bool :=
  let
    r := simplify r' in
  let
    s := simplify s' in
  
  orb (similar_left r s) (similar_left s r).

Example similar_t1 : true = similar EmptySet EmptySet.
Proof.
  unfold similar. simpl. reflexivity.
Qed.

Example similar_t2 : true = similar (App EmptySet (Char a)) EmptySet.
Proof.
  unfold similar. simpl. reflexivity.
Qed.

Example similar_t3 : true = similar (App (App (Char a) (Char b)) (Char c)) (App (Char a) (App (Char b) (Char c))).
Proof.
  unfold similar. unfold similar_left. simpl.
  rewrite <- Sigma_dec_refl with (a := a).
  rewrite <- Sigma_dec_refl with (a := b).
  rewrite <- Sigma_dec_refl with (a := c).
  simpl. reflexivity.
Qed.

Example similar_t4 : true = similar (Union (Union (Char a) (Char b)) (Char c)) (Union (Char a) (Union (Char b) (Char c))).
Proof.
  unfold similar. unfold similar_left. simpl.
  rewrite <- Sigma_dec_refl with (a := a).
  rewrite <- Sigma_dec_refl with (a := b).
  rewrite <- Sigma_dec_refl with (a := c).
  simpl. rewrite <- same_choice. simpl. reflexivity.
Qed.

Example similar_t5 : true = similar (Union (Char a) (Union (Char b) (Char c))) (Union (Union (Char a) (Char b)) (Char c)).
Proof.
  unfold similar. unfold similar_left. simpl.
  rewrite <- Sigma_dec_refl with (a := a).
  rewrite <- Sigma_dec_refl with (a := b).
  rewrite <- Sigma_dec_refl with (a := c).
  simpl. rewrite <- same_choice. rewrite <- or_true_true. reflexivity.
Qed.

Theorem sim_re_equiv : forall(r1 r2 : reg_exp) (s : list Sigma), matches r1 s -> similar r1 r2 -> matches r2 s.

                           
Fixpoint nullify (r : reg_exp) :=
  match r with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char _ => EmptyStr
  (* slightly different from paper, but equivalent I think *)
  | App r1 r2 => match nullify r1, nullify r2 with 
                | EmptyStr, EmptyStr => EmptyStr
                | _, _ => EmptySet
                end
  (* slightly different from paper, but equivalent I think *)
  | Union r1 r2 => match nullify r1, nullify r2 with
                  | EmptySet, EmptySet => EmptySet
                  | _, _ => EmptyStr
                  end
  | Star _ => EmptyStr
  end.

Fixpoint derivative (a : Sigma) (r : reg_exp) :=
  match r with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char x => if Sigma_dec x a then EmptyStr else EmptySet
  | App r1 r2 =>  Union (App (derivative a r1) r2) (App (nullify r1) (derivative a r2))
  | Union r1 r2 => Union (derivative a r1) (derivative a r2)
  | Star r => App (derivative a r) (Star r)
  end.

Fixpoint mu (r : reg_exp) (seen : list reg_exp) := 
  match r with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App r1 r2 => (mu r1 seen)
  | Union r1 r2 => (mu r1 seen) * (mu r2 seen)
  | Star r => mu r seen
  end.

Theorem der_decreasing : forall(a : Sigma) (r : reg_exp) (seen : list reg_exp), false = In_exact (derivative a r) seen -> mu (derivative a r) (r::seen) < mu r seen.
Proof.
  
  
(* This program would explore the entire tree of subsequent derivatives, 
where each branch is a character in the alphabet abet *)
Program Fixpoint Delta (abet : list Sigma) (a : Sigma)
        (r : reg_exp) (seen : list reg_exp) {measure (mu r seen)} : list reg_exp :=
  match In_exact (derivative a r) seen with
  | true => [r]
  | false => r::(flat_map (fun b => Delta abet b (derivative a r) (r::seen) ) abet)
  end.
  
Next Obligation.
  apply der_decreasing. apply Heq_anonymous.
Qed.

