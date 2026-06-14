(* analysis@home — work unit: consecutive-product-even (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). n*(n+1) is always even. *)

Require Import Arith Lia.

Theorem consecutive_even : forall n, exists k, n * (n + 1) = 2 * k.
Proof. induction n as [|m [k IH]].
  - exists 0. reflexivity.
  - exists (k + (m + 1)). nia. Qed.
