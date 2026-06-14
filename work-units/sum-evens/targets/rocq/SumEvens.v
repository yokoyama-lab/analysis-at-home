(* analysis@home — work unit: sum-evens (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The sum of the first n even numbers equals n(n+1). *)

Require Import Arith Lia.

Fixpoint sumeven (n : nat) : nat := match n with 0 => 0 | S m => sumeven m + 2 * (S m) end.
Theorem sum_evens : forall n, sumeven n = n * (n + 1).
Proof. induction n as [|m IH]; simpl; nia. Qed.
