(* analysis@home — work unit: sum-first-n-odds (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 1 + 3 + 5 + ... + (2n-1) = n^2. *)

Require Import Arith Lia.

Fixpoint oddsum (n : nat) : nat := match n with 0 => 0 | S m => oddsum m + (2 * m + 1) end.
Theorem sum_first_n_odds : forall n, oddsum n = n * n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
