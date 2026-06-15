(* analysis@home — work unit: comparison-sort-lower-bound (Rocq target).
 *
 * The information-theoretic lower bound for comparison sorting (TAOCP Vol. 3
 * §5.3.1). A comparison sort is a binary decision tree; to sort n elements it
 * must distinguish all n! permutations, so it has >= n! leaves. A binary tree of
 * height h has at most 2^h leaves (decision_tree_leaves_bound), hence
 *   n! <= leaves t <= 2^height t  =>  height t >= log2(n!) = Omega(n log n).
 * This promotes the `decision-tree-leaves-bound` core to the actual lg(n!) bound.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia Factorial.

Inductive bt := Lf | Nd (l r : bt).
Fixpoint leaves (t:bt) := match t with Lf => 1 | Nd l r => leaves l + leaves r end.
Fixpoint height (t:bt) := match t with Lf => 0 | Nd l r => S (Nat.max (height l) (height r)) end.

Lemma pow2_mono : forall a b, a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros a b H. induction H. lia. simpl. lia. Qed.

(* A binary decision tree of height h has at most 2^h leaves. *)
Lemma leaves_le_pow_height : forall t, leaves t <= 2 ^ height t.
Proof.
  induction t as [|l IHl r IHr]; simpl. lia.
  pose proof (pow2_mono (height l) (Nat.max (height l) (height r)) (Nat.le_max_l _ _)).
  pose proof (pow2_mono (height r) (Nat.max (height l) (height r)) (Nat.le_max_r _ _)).
  lia.
Qed.

(* Comparison-sort lower bound: any decision tree that distinguishes all n!
   orderings (>= n! leaves) has height >= log2(n!), i.e. makes >= lg(n!) ~ n lg n
   comparisons in the worst case. *)
Theorem comparison_sort_lower_bound :
  forall t n, fact n <= leaves t -> Nat.log2 (fact n) <= height t.
Proof.
  intros t n H.
  assert (Hp : fact n <= 2 ^ height t).
  { pose proof (leaves_le_pow_height t). lia. }
  apply Nat.log2_le_mono in Hp.
  rewrite Nat.log2_pow2 in Hp by apply Nat.le_0_l.
  exact Hp.
Qed.
