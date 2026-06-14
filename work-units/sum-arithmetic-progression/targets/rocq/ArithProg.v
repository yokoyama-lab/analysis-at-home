(* analysis@home — work unit: sum-arithmetic-progression (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Sum of a + (a+d) + ... + (a+(n-1)d) = n*a + d*n(n-1)/2. *)

Require Import Arith Lia.

Fixpoint sad (a d n:nat) := match n with 0=>0 | S m => sad a d m + (a + m*d) end.
Theorem sum_arithmetic_progression : forall a d n, 2 * sad a d n + d * n = 2 * n * a + d * n * n.
Proof. intros a d n. induction n as [|m IH]; simpl; nia. Qed.
