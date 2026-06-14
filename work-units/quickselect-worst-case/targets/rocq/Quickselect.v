(* analysis@home — work unit: quickselect-worst-case (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Quickselect worst case = n(n-1)/2 comparisons. *)

Require Import Arith Lia.
Fixpoint qsel_worst (n : nat) : nat := match n with 0 => 0 | S m => m + qsel_worst m end.
Theorem quickselect_worst_case : forall n, 2 * qsel_worst n + n = n * n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
