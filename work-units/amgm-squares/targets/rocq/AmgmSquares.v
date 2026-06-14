(* analysis@home — work unit: amgm-squares (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). AM-GM: twice the product is at most the sum of squares. *)

Require Import Arith Lia.

Theorem amgm_squares : forall a b, 2*a*b <= a*a + b*b.
Proof. intros a b. destruct (Nat.le_ge_cases a b) as [H|H]; nia. Qed.
