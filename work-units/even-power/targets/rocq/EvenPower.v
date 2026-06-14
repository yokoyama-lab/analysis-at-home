(* analysis@home — work unit: even-power (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). If a is even then a^(n+1) is even. *)

Require Import Arith Lia.

Theorem even_power : forall a n, (exists k, a = 2 * k) -> exists k, a ^ (S n) = 2 * k.
Proof. intros a n [k0 H]. exists (k0 * a ^ n). simpl. nia. Qed.
