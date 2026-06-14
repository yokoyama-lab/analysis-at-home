(* analysis@home — work unit: median-of-medians-linear (Rocq target). VERIFIED
   (Print Assumptions: closed under the global context). The median-of-medians
   (BFPRT) selection recurrence is linear: T(n) <= T(n/5) + T(7n/10) + n => T(n) <= 10n. *)

Require Import Arith Lia.

Lemma mul_div_le : forall a b, b <> 0 -> b * (a / b) <= a.
Proof. intros a b Hb. pose proof (Nat.div_mod a b Hb). lia. Qed.

(* Median-of-medians selection is worst-case LINEAR: any cost obeying the
   median-of-medians recurrence T(n) <= T(n/5) + T(7n/10) + n is <= 10n.
   The point is the contraction 1/5 + 7/10 = 9/10 < 1. *)
Theorem mom_linear :
  forall (T : nat -> nat),
    T 0 = 0 ->
    (forall n, T n <= T (n / 5) + T (7 * n / 10) + n) ->
    forall n, T n <= 10 * n.
Proof.
  intros T Hbase Hrec.
  assert (HB : forall fuel n, n <= fuel -> T n <= 10 * n).
  { induction fuel as [|f IH]; intros n Hn.
    - assert (n = 0) by lia. subst. rewrite Hbase. lia.
    - destruct (Nat.eq_dec n 0) as [->|Hpos].
      + rewrite Hbase. lia.
      + pose proof (mul_div_le n 5 ltac:(lia)) as D5.
        pose proof (mul_div_le (7 * n) 10 ltac:(lia)) as D7.
        assert (Hn5 : n / 5 <= f) by nia.
        assert (Hn7 : 7 * n / 10 <= f) by nia.
        pose proof (IH (n / 5) Hn5) as A.
        pose proof (IH (7 * n / 10) Hn7) as B.
        pose proof (Hrec n) as R.
        nia. }
  intro n. apply (HB n n). lia.
Qed.
