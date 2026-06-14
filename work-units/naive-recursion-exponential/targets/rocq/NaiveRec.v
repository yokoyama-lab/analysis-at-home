(* analysis@home — work unit: naive-recursion-exponential (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A recursion that doubles its subproblems each level (no memoization) has 2^k - 1 calls. *)

Require Import Arith Lia.

Theorem naive_recursion_exponential :
  forall (T : nat -> nat), T 0 = 0 -> (forall k, T (S k) = 2 * T k + 1) -> forall k, T k + 1 = 2 ^ k.
Proof. intros T H0 Hrec. induction k as [|m IH].
  - rewrite H0. reflexivity.
  - assert (E : 2 ^ (S m) = 2 * 2 ^ m) by reflexivity. rewrite Hrec. lia. Qed.
