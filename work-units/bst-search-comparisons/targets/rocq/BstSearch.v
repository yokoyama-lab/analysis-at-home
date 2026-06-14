(* analysis@home — work unit: bst-search-comparisons (Rocq target)
 *
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: worst-case.
 *
 * TAOCP Vol. 3 §6.2.2 — searching a binary search tree. The number of key
 * comparisons along the search path is at most the height of the tree:
 *
 *   bst_search_comparisons : snd (search x t) <= height t.
 *
 * Corollary (balanced trees): a balanced BST on n keys has height O(log n), so
 * search costs O(log n) comparisons — the binary-search bound (Vol. 3 §6.2.1).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

Inductive tree : Type := Leaf | Node (l : tree) (k : nat) (r : tree).

Fixpoint height (t : tree) : nat :=
  match t with Leaf => 0 | Node l _ r => S (Nat.max (height l) (height r)) end.

Fixpoint search (x : nat) (t : tree) : bool * nat :=
  match t with
  | Leaf => (false, 0)
  | Node l k r =>
      if x =? k then (true, 1)
      else if x <? k then let '(b, c) := search x l in (b, S c)
           else let '(b, c) := search x r in (b, S c)
  end.

Theorem bst_search_comparisons : forall t x, snd (search x t) <= height t.
Proof.
  induction t as [|l IHl k r IHr]; intro x.
  - simpl. lia.
  - simpl. destruct (x =? k).
    + cbn [snd]. lia.
    + destruct (x <? k).
      * destruct (search x l) as [b c] eqn:E. cbn [snd].
        specialize (IHl x). rewrite E in IHl. cbn [snd] in IHl.
        pose proof (Nat.le_max_l (height l) (height r)). lia.
      * destruct (search x r) as [b c] eqn:E. cbn [snd].
        specialize (IHr x). rewrite E in IHr. cbn [snd] in IHr.
        pose proof (Nat.le_max_r (height l) (height r)). lia.
Qed.
