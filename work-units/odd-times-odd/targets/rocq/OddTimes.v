(* analysis@home — work unit: odd-times-odd (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The product of two odd numbers is odd. *)

Require Import Arith Lia.

Theorem odd_times_odd_odd : forall a b, (exists k, a=2*k+1) -> (exists k, b=2*k+1) -> exists k, a*b = 2*k+1.
Proof. intros a b [ka Ha] [kb Hb]. exists (2*ka*kb + ka + kb). nia. Qed.
