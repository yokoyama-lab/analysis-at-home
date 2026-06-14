(* analysis@home — work unit: gauss-sum (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The arithmetic series 1+2+...+n = n(n+1)/2 (Gauss). *)

Require Import Arith Lia.

Fixpoint sum_upto (n : nat) : nat := match n with 0 => 0 | S m => sum_upto m + S m end.
Theorem gauss_sum : forall n, 2 * sum_upto n = n * (n + 1).
Proof. induction n as [|m IH]; [reflexivity | simpl; nia]. Qed.
