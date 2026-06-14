(* analysis@home — work unit: square-of-sum (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The binomial square identity. *)

Require Import Arith Lia.

Theorem square_of_sum : forall a b, (a+b)*(a+b) = a*a + 2*a*b + b*b.
Proof. intros a b. ring. Qed.
