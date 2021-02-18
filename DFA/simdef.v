Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From VLG Require Import ltac.
From VLG Require Import sigma.
From VLG Require Import matcher.
From VLG Require Import regexNotations.

Inductive re_sim_prop : regex -> regex ->  Prop
  :=
    u_self1 (r : regex) : re_sim_prop (Union r r) r
  | u_self2 (r : regex) : re_sim_prop r (Union r r)
  | u_comm1 (r s : regex) : re_sim_prop (Union r s) (Union s r)
  | u_comm2 (r s : regex) : re_sim_prop (Union s r) (Union r s)
  | u_assoc1 (r s t : regex) :
      re_sim_prop (Union (Union r s) t) (Union r (Union s t))
  | u_assoc2 (r s t : regex) :
      re_sim_prop (Union r (Union s t)) (Union (Union r s) t)
  | a_assoc1 (r s t : regex) :
      re_sim_prop (App (App r s) t) (App r (App s t))
  | a_assoc2 (r s t : regex) :
      re_sim_prop (App r (App s t)) (App (App r s) t)
  (** * *Distributivity
  | au_dist1 (r s t : regex) :
      re_sim_prop (App (Union r s) t) (Union (App r t) (App s t))
  | au_dist2 (r s t : regex) :
      re_sim_prop (Union (App r t) (App s t)) (App (Union r s) t)
      *)
  | sim_refl (r : regex) : re_sim_prop r r.


Definition re_sim (e1 e2 : regex) : bool :=
  (e1 = e2)                                       (* sim refl *)
  || match e1, e2 with
    | (r1 # s1) # (t1 # u1), (r2 # s2) # (t2 # u2) =>
      (  (e1 = (r2 # s2)) && (e1 = (t2 # u2))  ) (* self union *)
      || (  (e2 = (r1 # s1)) && (e2 = (t1 # u1))  ) (* self union *)
      || (  ((r1 # s1) = (t2 # u2)) && ((t1 # u1) = (r2 # s2))  ) (* union commutes *)
      (** treat (r1 # s1) as r1 and (t2 # u2) as t2, as in case 2 **)
      || (  ((r1 # s1) = r2) && (t1 = s2) && (u1 = (t2 # u2))  ) (* union assoc *)
      (** treat (r2 # s2) as r2 and (t1 # u1) as t1, as in case 3 **)
      || (  (r1 = (r2 # s2)) && (s1 = t2) && ((t1 # u1) = u2)  ) (* union assoc *)
    (* * case 2 * *)
    | r1 # (s1 # t1), (r2 # s2) # t2 =>
      (  (e1 = (r2 # s2)) && (e1 = t2)  )          (* self union *)
      || (  (e2 = r1) && (e2 = (s1 # t1))  )        (* self union *)
      || (  (r1 = t2) && ((s1 # t1) = (r2 # s2))  ) (* union commutes *)
      || (  (r1 = r2) && (s1 = s2) && (t1 = t2)  )  (* union assoc *)
    (* * case 3 * *)
    | (r1 # s1) # t1, r2 # (s2 # t2) =>
      (  (e1 = r2) && (e1 = (s2 # t2))  )          (* self union *)
      || (  (e2 = (r1 # s1)) && (e2 = t1)  )        (* self union *)
      || (  ((r1 # s1) = (s2 # t2)) && (t1 = r2)  ) (* union commutes *)
      || (  (r1 = r2) && (s1 = s2) && (t1 = t2)  )  (* union assoc *)
    | r1 # s1, s2 # r2 =>
      (  (e1 = r2) && (e1 = s2)  )                 (* self union *)
      || (  (e2 = r1) && (e2 = s1)  )                (* self union *)
      || (  (r1 = r2) && (s1 = s2)  )                (* union commutes *)
      (** * *Distributivity
    | (r1 # s1) @ t0, (r2 @ t1) # (s2 @ t2) =>
      (  (e1 = (r2 @ t1)) && (e1 = (s2 @ t2))  )    (* self union *)
      || (  (r1 = r2) && (s1 = s2)
           && (t0 = t1) && (t0 = t2)  )   (* app distr over union *)
    | (r1 @ t0) # (s1 @ t1), (r2 # s2) @ t2 =>
      (  (e2 = (r1 @ t0)) && (e2 = (s1 @ t1))  )    (* self union *)
      || (  (r1 = r2) && (s1 = s2)
           && (t0 = t1) && (t0 = t2)  )   (* app distr over union *)
       *)
    | r0 # r1, _ =>
      (  (e2 = r0) && (e2 = r1)  )                  (* self union *)
    | _, r0 # r1 =>
      (  (e1 = r0) && (e1 = r1)  )                  (* self union *)
    | (r1 @ s1) @ (t1 @ u1), (r2 @ s2) @ (t2 @ u2) =>
      (  ((r1 @ s1) = r2) && (t1 = s2) && (u1 = (t2 @ u2))  )
      || (  (r1 = (r2 @ s2)) && (s1 = t2) && ((t1 @ u1) = u2)  )
    | r1 @ (s1 @ t1), (r2 @ s2) @ t2 =>
      (  (r1 = r2) && (s1 = s2) && (t1 = t2)  )     (* assoc commutes *)                           
    | (r1 @ s1) @ t1, r2 @ (s2 @ t2) => 
      (  (r1 = r2) && (s1 = s2) && (t1 = t2)  )     (* assoc commutes *)   
    | _, _ => false
    end.

