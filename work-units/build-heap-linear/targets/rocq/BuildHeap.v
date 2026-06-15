(* analysis@home — work unit: build-heap-linear (Rocq target).
 *
 * Floyd's build-heap is O(n), not O(n log n) (TAOCP Vol. 3 §5.2.3). Sift-down at
 * a node of height j costs O(j); summed over a perfect binary tree of height h,
 * the TOTAL work is the sum of all node heights:
 *   sheight h = (root height) S h' + 2 * sheight h'.
 * The surprising fact is that this sum is LINEAR in the number of nodes:
 *   sheight h + h + 1 = nodes h          (build_heap_identity)
 *   sheight h <= nodes h                 (build_heap_le_nodes)
 * with nodes h + 1 = 2^(h+1) (nodes_pow), i.e. total sift-down work <= n. The
 * geometric series sum_{j>=1} j/2^j = 2 converges, so the heights don't add up to
 * n log n.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

(* number of nodes of a perfect binary tree of height h (= 2^(h+1) - 1) *)
Fixpoint nodes (h:nat) : nat := match h with 0 => 1 | S h' => 1 + 2 * nodes h' end.
(* sum of the heights of all nodes of a perfect binary tree of height h *)
Fixpoint sheight (h:nat) : nat := match h with 0 => 0 | S h' => S h' + 2 * sheight h' end.

Lemma nodes_pow : forall h, nodes h + 1 = 2 ^ (S h).
Proof.
  induction h as [|h' IH]; [reflexivity|].
  rewrite (Nat.pow_succ_r' 2 (S h')). cbn [nodes]. lia.
Qed.

(* The heart of "build-heap is linear": the total sift-down work equals the node
   count minus (h+1). *)
Theorem build_heap_identity : forall h, sheight h + h + 1 = nodes h.
Proof.
  induction h as [|h' IH]; [reflexivity|].
  cbn [sheight nodes]. lia.
Qed.

Corollary build_heap_le_nodes : forall h, sheight h <= nodes h.
Proof. intro h. pose proof (build_heap_identity h). lia. Qed.
