(* analysis@home — work unit: double-is-even (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Doubling any number gives an even number. *)

Require Import Arith Lia.
Theorem double_is_even : forall n, exists k, n + n = 2 * k.
Proof. intro n. exists n. lia. Qed.
