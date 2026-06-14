(* analysis@home — work unit: odd-plus-odd-even (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The sum of two odd numbers is even. *)

Require Import Arith Lia.

Theorem odd_plus_odd_even : forall a b, (exists k, a = 2*k+1) -> (exists k, b = 2*k+1) -> exists k, a + b = 2*k.
Proof. intros a b [ka Ha] [kb Hb]. exists (ka + kb + 1). lia. Qed.
