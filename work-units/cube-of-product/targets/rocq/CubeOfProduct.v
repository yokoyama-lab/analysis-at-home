(* analysis@home — work unit: cube-of-product (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Powers distribute over products (cubes). *)

Require Import Arith Lia.

Theorem cube_of_product : forall a b, (a*b)*(a*b)*(a*b) = (a*a*a)*(b*b*b).
Proof. intros a b. ring. Qed.
