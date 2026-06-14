(* analysis@home — work unit: geometric-recursion-count (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A divide-and-conquer making a recursive calls per level has a^k subproblems at depth k (Karatsuba a=3, Strassen a=7, Toom-3 a=5). *)

Require Import Arith Lia.

Theorem geometric_recursion_count :
  forall (a : nat) (M : nat -> nat), M 0 = 1 -> (forall k, M (S k) = a * M k) -> forall k, M k = a ^ k.
Proof. intros a M H0 Hrec. induction k as [|m IH]; simpl. exact H0. rewrite Hrec, IH. reflexivity. Qed.
