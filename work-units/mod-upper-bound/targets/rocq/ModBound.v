(* analysis@home — work unit: mod-upper-bound (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A remainder is strictly smaller than a nonzero divisor. *)

Require Import Arith Lia.
Theorem mod_upper_bound_succ : forall a b, a mod (S b) < S b.
Proof. intros a b. apply Nat.mod_upper_bound. lia. Qed.
