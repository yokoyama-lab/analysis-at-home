(* analysis@home — work unit: two-pow-positive (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 2^n is at least 1 for all n. *)

Require Import Arith Lia.

Theorem two_pow_positive : forall n, 1 <= 2 ^ n.
Proof. induction n as [|m IH]; simpl; lia. Qed.
