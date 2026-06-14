(* analysis@home — work unit: linear-search-best-case (Rocq target)
 *
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: best-case.
 *
 * The best case of linear search: on any NON-EMPTY list, at least one key
 * comparison is performed (the match can be found no faster than examining the
 * first element). This is the universal lower bound; it is achieved exactly when
 * the target sits in the head position.
 *
 * Together with linear-search-comparisons (worst case: <= n) this brackets the
 * cost: 1 <= cost <= n on non-empty inputs.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint lsearch (x : nat) (l : list nat) : bool * nat :=
  match l with
  | [] => (false, 0)
  | y :: ys => if x =? y then (true, 1) else let '(b, c) := lsearch x ys in (b, S c)
  end.

Theorem linear_search_best_case :
  forall x l, 1 <= length l -> 1 <= snd (lsearch x l).
Proof.
  intros x l Hlen. destruct l as [|y ys].
  - simpl in Hlen. lia.
  - simpl. destruct (x =? y).
    + simpl. lia.
    + destruct (lsearch x ys) as [b c]. simpl. lia.
Qed.
