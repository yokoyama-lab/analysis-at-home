(* analysis@home — work unit: amgm-four-ab (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). AM-GM: four times the product is at most the squared sum. *)

Require Import Arith Lia.

Theorem amgm_four_ab : forall a b, 4*a*b <= (a+b)*(a+b).
Proof. intros a b. destruct (Nat.le_ge_cases a b) as [H|H]; nia. Qed.
