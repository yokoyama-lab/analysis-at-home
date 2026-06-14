(* analysis@home — work unit: cube-of-sum (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The binomial cube expansion. *)

Require Import Arith Lia.

Theorem cube_of_sum : forall a b, (a+b)*(a+b)*(a+b) = a*a*a + 3*a*a*b + 3*a*b*b + b*b*b.
Proof. intros a b. ring. Qed.
