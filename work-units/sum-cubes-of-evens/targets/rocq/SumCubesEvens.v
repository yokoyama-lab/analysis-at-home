(* analysis@home — work unit: sum-cubes-of-evens (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). (2)^3 + (4)^3 + ... + (2n)^3 = 2(n(n+1))^2. *)

Require Import Arith Lia.

Fixpoint sce (n:nat) := match n with 0=>0 | S m => sce m + ((2*(S m))*(2*(S m))*(2*(S m))) end.
Theorem sum_cubes_of_evens : forall n, sce n = 2 * (n*(n+1)) * (n*(n+1)).
Proof. induction n as [|m IH]; simpl; nia. Qed.
