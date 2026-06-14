(* analysis@home — work unit: linear-search-average-comparisons (Rocq target)
 *
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: expected-cost.
 * Input distribution: the target is present and equally likely to be any one of
 * the n list positions (uniform present target).
 *
 * This is the VERIFY-TRACK TWIN of the conjecture-track result
 * tools/conjecture/results/linear-search.json, which computes
 *   E[comparisons(n)] = (n+1)/2  and  limit law = Uniform.
 * Here we PROVE the exact mean, in two axiom-free pieces:
 *
 *   (1) lsearch_at — the cost model grounding: if the target first matches at
 *       1-based position p (a prefix of p-1 non-matches, then the target), linear
 *       search performs exactly p comparisons.  So the cost at position p is p.
 *
 *   (2) linear_search_avg_total — summing p over the n equally likely positions
 *       gives sum_upto n, and 2 * sum_upto n = n*(n+1).  Hence the average
 *       cost is exactly (n+1)/2 (stated without division to stay in nat).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint lsearch (x : nat) (l : list nat) : bool * nat :=
  match l with
  | [] => (false, 0)
  | y :: ys => if x =? y then (true, 1) else let '(b, c) := lsearch x ys in (b, S c)
  end.

(* (1) Cost-model grounding: matching at 1-based position S (length pref) costs
   exactly S (length pref) comparisons. *)
Lemma lsearch_at :
  forall x pref l,
    (forall y, In y pref -> x =? y = false) ->
    snd (lsearch x (pref ++ x :: l)) = S (length pref).
Proof.
  intros x pref l Hpref. induction pref as [|y ys IH].
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - assert (Hxy : x =? y = false) by (apply Hpref; left; reflexivity).
    assert (Hys : forall z, In z ys -> x =? z = false)
      by (intros z Hz; apply Hpref; right; exact Hz).
    specialize (IH Hys).
    simpl. rewrite Hxy.
    destruct (lsearch x (ys ++ x :: l)) as [b c] eqn:E. simpl.
    try (rewrite E in IH). simpl in IH. lia.
Qed.

(* (2) Sum of the per-position costs 1 + 2 + ... + n. *)
Fixpoint sum_upto (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => sum_upto m + S m
  end.

Theorem linear_search_avg_total : forall n, 2 * sum_upto n = n * (n + 1).
Proof.
  induction n as [|m IH].
  - reflexivity.
  - simpl. nia.
Qed.
