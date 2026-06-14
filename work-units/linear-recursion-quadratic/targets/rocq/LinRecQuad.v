(* analysis@home — work unit: linear-recursion-quadratic (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). T(n)=T(n-1)+n gives n(n+1)/2 (e.g. insertion sort's total comparisons). *)

Require Import Arith Lia.

Theorem linear_recursion_quadratic :
  forall (T : nat -> nat), T 0 = 0 -> (forall k, T (S k) = T k + S k) -> forall k, 2 * T k = k * (k + 1).
Proof. intros T H0 Hrec. induction k as [|m IH]. rewrite H0. reflexivity. rewrite Hrec. nia. Qed.
