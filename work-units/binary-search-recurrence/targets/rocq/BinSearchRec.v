(* analysis@home — work unit: binary-search-recurrence (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Halving with O(1) work per level makes k = lg n probes on a 2^k array. *)

Require Import Arith Lia.

Theorem binary_search_recurrence :
  forall (T : nat -> nat), T 0 = 0 -> (forall k, T (S k) = T k + 1) -> forall k, T k = k.
Proof. intros T H0 Hrec. induction k as [|m IH]. exact H0. rewrite Hrec, IH. lia. Qed.
