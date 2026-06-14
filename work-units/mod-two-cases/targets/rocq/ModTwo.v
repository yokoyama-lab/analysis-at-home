(* analysis@home — work unit: mod-two-cases (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The remainder mod 2 is 0 or 1. *)

Require Import Arith Lia.

Theorem mod_two_lt : forall n, n mod 2 < 2.
Proof. intro n. apply Nat.mod_upper_bound. lia. Qed.
