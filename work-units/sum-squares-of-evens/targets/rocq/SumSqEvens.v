(* analysis@home — work unit: sum-squares-of-evens (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). (2)^2 + (4)^2 + ... + (2n)^2 = 2n(n+1)(2n+1)/3. *)

Require Import Arith Lia.

Fixpoint sse (n:nat) := match n with 0 => 0 | S m => sse m + (2*(S m))*(2*(S m)) end.
Theorem sum_squares_of_evens : forall n, 3 * sse n = 2 * n * (n + 1) * (2 * n + 1).
Proof. induction n as [|m IH]; simpl; nia. Qed.
