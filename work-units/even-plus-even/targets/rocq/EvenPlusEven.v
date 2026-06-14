(* analysis@home — work unit: even-plus-even (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The sum of two even numbers is even. *)

Require Import Arith Lia.

Theorem even_plus_even : forall a b, (exists k, a = 2*k) -> (exists k, b = 2*k) -> exists k, a + b = 2*k.
Proof. intros a b [ka Ha] [kb Hb]. exists (ka + kb). lia. Qed.
