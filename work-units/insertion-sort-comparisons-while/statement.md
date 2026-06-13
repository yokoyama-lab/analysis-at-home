# Worst-case key-comparison count of insertion sort (WHILE)

## Informal claim

Insertion sort, written **imperatively in a small WHILE language** (mutable
array + scalar variables, nested loops), sorts a list of length `n` using at
most

> `n(n − 1) / 2` **key comparisons**,

equivalently (division-free):

> `2 · k ≤ n · (n − 1)`  for every terminating run that performs `k` key comparisons.

## What "key comparison" means here

The cost model is **`while-ops`** with `counts = ["key-comparison"]`. In the
fixed semantics ([`targets/rocq/InsertionSortWhileComparisons.v`](targets/rocq/InsertionSortWhileComparisons.v)):

- Boolean evaluation `beval` returns `(value, #key-comparisons)`.
- Only the **`BKLe`** form — comparing an array element to the held `key` — costs
  **1**. Index/bookkeeping tests (`BLe`, e.g. `1 <= j`, `i < n`) cost **0**.
- The big-step relation `ceval c s s' k` means "running `c` from state `s`
  terminates in `s'` having performed `k` key comparisons."

This mirrors classic analysis of algorithms, which counts a single **dominant
operation** rather than all elementary steps.

## Why this unit exists

It is the **same theorem** as the functional unit
[`insertion-sort-comparisons`](../insertion-sort-comparisons/) (`func-ops`,
structural-recursion instrumentation), but under the **`while-ops`** cost model.
Together the two units demonstrate:

1. the `cost_model` parameter is real and discriminating, and
2. an asymptotic claim is **robust across formulations** — functional vs.
   imperative — which is exactly the kind of cross-model agreement the project
   wants to make machine-checked.

The WHILE core is also the on-ramp to imperative and **reversible** (R-WHILE /
Janus-style) algorithms, whose cost analysis is a planned differentiating
sub-corpus.

## Proof sketch (for the contributor)

Each inner-loop guard evaluation with `j ≥ 1` performs exactly one key
comparison; for the element at index `i` the inner loop tests at most positions
`j = i, i−1, …, 1`, i.e. ≤ `i` comparisons. Summing over the outer loop
`i = 1 … n−1` gives `Σ i = n(n−1)/2`. Bookkeeping tests are free, so they do not
enter the count. A lemma bounding the inner loop's comparisons by the initial
value of `j`, plus induction on the outer loop, should discharge it.

## References

Pointers for context — do **not** copy prose into the corpus.

- Neil D. Jones, *Computability and Complexity from a Programming Perspective*.
- Nielson & Nielson, *Semantics with Applications* (cost-annotated semantics).
