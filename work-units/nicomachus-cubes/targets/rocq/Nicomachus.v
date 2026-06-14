(* analysis@home — work unit: nicomachus-cubes (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Sum of first n cubes = (sum of first n)^2. *)

Require Import Arith Lia.

Fixpoint sumcube (n : nat) : nat := match n with 0 => 0 | S m => sumcube m + (S m) * (S m) * (S m) end.
Theorem nicomachus : forall n, 4 * sumcube n = (n * (n + 1)) * (n * (n + 1)).
Proof. induction n as [|m IH]; simpl; nia. Qed.
