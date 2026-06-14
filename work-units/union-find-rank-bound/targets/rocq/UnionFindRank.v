(* analysis@home — work unit: union-find-rank-bound (Rocq target). VERIFIED (Print
   Assumptions: closed under the global context). A union-by-rank tree of rank r has at
   least 2^r elements, so its rank (= find depth) is at most lg n: find is O(log n). *)

Require Import Arith Lia.

Fixpoint uf_minsize (r : nat) : nat := match r with 0 => 1 | S r' => 2 * uf_minsize r' end.
Theorem union_find_rank_bound : forall r, uf_minsize r = 2 ^ r.
Proof. induction r as [|r' IH]; simpl. reflexivity. rewrite IH. reflexivity. Qed.
