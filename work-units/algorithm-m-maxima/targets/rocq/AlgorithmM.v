(* analysis@home — work unit: algorithm-m-maxima (Rocq target)
 *
 * Cost model: func-ops / counts = ["max-update"].  claim_kind: worst-case.
 *
 * TAOCP Vol. 1 §1.2.10 — Algorithm M (finding the maximum), Knuth's canonical
 * example of average-case analysis. Scanning left to right keeping a running
 * maximum, count how many times it is updated ("k := j"). `lr_changes cur l`
 * counts the updates while scanning l against an initial maximum cur.
 *
 * Worst case: at most one update per scanned element (attained by a strictly
 * increasing input, seeded below it):
 *   lr_changes cur l <= length l.
 *
 * The AVERAGE number of updates over a random permutation is H_n − 1 (and the
 * number of left-to-right maxima is H_n) — see the conjecture-track artifact
 * tools/conjecture/results/algorithm-m-maxima.json. That harmonic average is a
 * candidate future kernel twin (we already verify harmonic numbers in
 * quicksort-average-comparisons).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint lr_changes (cur : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => if cur <? x then S (lr_changes x xs) else lr_changes cur xs
  end.

Theorem algorithm_m_changes_le : forall l cur, lr_changes cur l <= length l.
Proof.
  induction l as [|x xs IH]; intro cur.
  - simpl. lia.
  - simpl. destruct (cur <? x).
    + specialize (IH x). lia.
    + specialize (IH cur). lia.
Qed.
