(* analysis@home — work unit: decision-tree-leaves-bound (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A binary tree of height h has <= 2^h leaves (the comparison-sort lower-bound core). *)

Require Import Arith Lia.
Inductive bt := Lf | Nd (l r : bt).
Fixpoint leaves (t:bt) := match t with Lf => 1 | Nd l r => leaves l + leaves r end.
Fixpoint height (t:bt) := match t with Lf => 0 | Nd l r => S (Nat.max (height l) (height r)) end.

Lemma pow2_mono : forall a b, a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros a b H. induction H. lia. simpl. lia. Qed.

(* A binary decision tree of height h has at most 2^h leaves. This is the heart
   of the comparison-sort lower bound: a comparison sort's decision tree must
   have >= n! leaves, so its height (worst-case comparisons) is >= lg(n!). *)
Theorem decision_tree_leaves_bound : forall t, leaves t <= 2 ^ height t.
Proof.
  induction t as [|l IHl r IHr]; simpl. lia.
  pose proof (pow2_mono (height l) (Nat.max (height l) (height r)) (Nat.le_max_l _ _)).
  pose proof (pow2_mono (height r) (Nat.max (height l) (height r)) (Nat.le_max_r _ _)).
  lia.
Qed.
