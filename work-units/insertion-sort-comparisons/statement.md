# Worst-case comparison count of insertion sort

## Informal claim

Let `isort` be insertion sort on lists of natural numbers, instrumented to count
the number of **key comparisons** it performs (each `x <=? y` test counts as
one). For every input list `l` of length `n`,

> `comparisons(l) ≤ n(n − 1) / 2`.

To avoid division in the formal statement, prove the equivalent integer form:

> `2 · comparisons(l) ≤ n · (n − 1)`.

This worst case is attained by a strictly descending list.

## Why this unit

- It pairs cleanly with the **functional-correctness** unit ("`isort` returns a
  sorted permutation"), giving the project its first _correctness + cost_ pair.
- The bound is small and self-contained — ideal for pushing one theorem
  end-to-end through submit → kernel-verify → corpus.
- The instrumented `insert` does at most `length l` comparisons; summing over
  the `n` insertions gives the `n(n−1)/2` bound. A clean induction.

## Reference cost model

A reference instrumented implementation (the cost model the claim is about)
lives in [`targets/rocq/InsertionSortComparisons.v`](targets/rocq/InsertionSortComparisons.v):
`insert` returns `(new_list, comparisons_used)` and `isort` sums the counts.

Other backends (`lean`, `agda`) should mirror this exact cost model so the
claim means the same thing across kernels.

## References

These are pointers for context — do **not** copy textbook prose into the corpus.

- Software Foundations, Vol. 3 (Appel): functional correctness of insertion sort in Rocq.
- Charguéraud & Pottier, "A Fistful of Dollars": formal asymptotic cost via time credits.
