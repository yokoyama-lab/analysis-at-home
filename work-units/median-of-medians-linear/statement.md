# Median-of-medians selection is worst-case linear

> *Blum–Floyd–Pratt–Rivest–Tarjan (1973); TAOCP Vol. 3 §5.3.3.*

## Claim
The median-of-medians (BFPRT) selection algorithm splits into groups of 5, recurses
on the median-of-medians (size `n/5`) to pick a pivot, partitions, and recurses on
the larger side (size at most `7n/10`). Its comparison cost therefore obeys
> `T(n) <= T(n/5) + T(7n/10) + n`,

and we prove this forces **linear** total work:
> `T 0 = 0  ->  (forall n, T n <= T(n/5) + T(7n/10) + n)  ->  forall n, T n <= 10 * n`.

## Why it works
The two recursive sizes contract: `1/5 + 7/10 = 9/10 < 1`. Plugging the linear
ansatz `T(m) <= 10m`: `10*(n/5) + 10*(7n/10) + n <= 2n + 7n + n = 10n`. The proof is
a bounded (fuel) strong induction; the per-step inequality `10*(n/5) <= 2n` and
`10*(7n/10) <= 7n` come from `b*(a/b) <= a`.

This is the heart of **worst-case linear selection**, stated as a verified theorem
about the recurrence (the full algorithm model is a larger separate effort).

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof (`mom_linear`, axiom-free):
[`targets/rocq/MedianOfMedians.v`](targets/rocq/MedianOfMedians.v).
