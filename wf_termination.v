Require Import Arith.Wf_nat List PeanoNat Program.Wf.
Import ListNotations.

(* This function for computing the minimum number in a list
   is acceptable in OCaml.
   
   let rec weird_min xs =
     match xs with 
     | [] -> 0
     | [x] -> x
     | x :: y :: zs -> weird_min (min x y :: zs)

 *)

(* But Coq rejects it. *)
Fail Fixpoint weird_min (xs : list nat) : nat :=
  match xs with
  | []           => 0
  | [x]          => x
  | x :: y :: zs => weird_min (Nat.min x y :: zs)
  end.
(* The termination checker can't figure out that 
   (Nat.min x y :: zs) is smaller than (x :: y :: zs) *)

(* We can define it with Program Fixpoint. *)
Program Fixpoint weird_min (xs : list nat)
                           {measure (length xs)} : nat :=
  match xs with
  | []           => 0
  | [x]          => x
  | x :: y :: zs => weird_min (Nat.min x y :: zs)
  end.

(* Suppose we don't want to use Program Fixpoint --
   because we don't like the unfolding behavior, for example.

   In that case, we can use well-founded recursion. 

   We give the function an extra parameter: a proof that
   some measure of the other parameters is accessible
   in some well-founded relation.

   Then we say that the function is structurally recursive
   on the size of that proof.
   *)
Fixpoint weird_min (xs : list nat)
                   (Ha : Acc lt (length xs))
                   {struct Ha} : nat.
  refine (match xs with
          | []           => 0
          | [x]          => x
          (* The underscore below stands for the Acc proof
             in the recursive call *)
          | x :: y :: zs => weird_min (Nat.min x y :: zs) _
          end).
  (* There's a problem, though -- 
     we need the fact that xs = x :: y :: zs,
     but it's not in the context. *)
Abort.

(* We have to use something called the convoy pattern. *)
Fixpoint weird_min' (xs : list nat)
                    (Ha : Acc lt (length xs))
                    {struct Ha} : nat.
  refine (match xs as xs' return xs = xs' -> _ with
          | []           => fun _   => 0
          | [x]          => fun _   => x
          | x :: y :: zs => fun Heq => weird_min' (Nat.min x y :: zs) _
          end eq_refl).
  (* Now the needed fact is in the context as Heq *)
  subst.
  apply Acc_inv with (x := length (x :: y :: zs)).
  - auto.
  - simpl.
    (* Now it's easy to see that (min x y :: zs) 
       is shorter than (x :: y :: zs) *)
    auto.
Defined.

(* We can also define the Acc proof externally *)

Lemma tail_acc :
  forall xs x y zs,
    xs = x :: y :: zs
    -> Acc lt (length xs)
    -> Acc lt (length (Nat.min x y :: zs)).
Proof.
  intros xs x y zs ? Ha; subst.
  eapply Acc_inv; eauto.
Defined.

(* Now we don't have to use refine *)
Fixpoint weird_min'' (xs : list nat)
                     (Ha : Acc lt (length xs))
                     {struct Ha} : nat := 
  match xs as xs' return xs = xs' -> _ with
  | []           => fun _   => 0
  | [x]          => fun _   => x
  | x :: y :: zs => fun Heq =>
                      weird_min'' (Nat.min x y :: zs)
                                  (tail_acc xs x y zs Heq Ha)
  end eq_refl.

(* We can write an unfolding lemma for the function *)
Lemma unfold_weird_min'' :
  forall xs Ha,
    weird_min'' xs Ha =
    match xs as xs' return xs = xs' -> _ with
    | []           => fun _   => 0
    | [x]          => fun _   => x
    | x :: y :: zs => fun Heq =>
                        weird_min'' (Nat.min x y :: zs)
                                    (tail_acc xs x y zs Heq Ha)
    end eq_refl.
Proof.
  intros xs Ha; unfold weird_min''; simpl.
  destruct Ha; destruct xs; auto.
Qed.

(* If we extract the program to OCaml, we get something reasonable --
   all of the termination-related proof terms disappear *)
Extraction weird_min''.
