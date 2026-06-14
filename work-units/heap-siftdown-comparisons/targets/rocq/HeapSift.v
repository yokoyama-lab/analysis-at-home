(* analysis@home — work unit: heap-siftdown-comparisons (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Heap sift-down: at most 2 * height comparisons. *)

Require Import Arith Lia.
Inductive tree := Leaf | Node (l r : tree).
Fixpoint height (t:tree) := match t with Leaf => 0 | Node l r => S (Nat.max (height l) (height r)) end.
Fixpoint sift (t:tree) : nat := match t with Leaf => 0 | Node l r => 2 + Nat.max (sift l) (sift r) end.
Theorem heap_siftdown_comparisons : forall t, sift t <= 2 * height t.
Proof. induction t as [|l IHl r IHr]; simpl. lia.
  pose proof (Nat.le_max_l (height l) (height r));
  pose proof (Nat.le_max_r (height l) (height r)).
  assert (Nat.max (sift l) (sift r) <= 2 * Nat.max (height l) (height r)) by (apply Nat.max_lub; lia).
  lia. Qed.
