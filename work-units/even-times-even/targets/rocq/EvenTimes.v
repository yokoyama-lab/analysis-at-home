(* analysis@home — work unit: even-times-even (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). An even factor makes the product even. *)

Require Import Arith Lia.

Theorem even_times_even : forall a b, (exists k, a = 2*k) -> exists k, a*b = 2*k.
Proof. intros a b [k Hk]. exists (k*b). nia. Qed.
