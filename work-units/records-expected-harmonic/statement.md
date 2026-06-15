# Expected number of records = H_n (Algorithm M, average case)

> *TAOCP Vol. 1 §1.2.10.* The deep average-case result of the corpus: the verified
> twin of the enumerated [`algorithm-m-maxima.json`](../../tools/conjecture/results/algorithm-m-maxima.json),
> checked against it by the faithfulness oracle.

## Claim
The expected number of left-to-right maxima (records) of a uniformly random
permutation of `[n]` is the harmonic number `H_n`:

> **`records_expected`**: `E records (ranks n) == harmonic n`.

## Method (no enumeration of the n! outcomes)
Uniform permutations are modelled by their **sequential-rank vectors** (Rényi):
`c = (c_1..c_n)` with `c_i ∈ {1..i}`, uniform, `|ranks n| = n!`. Position `i` is a
record iff `c_i = i`. **Linearity over the last coordinate** gives the recurrence

> `Tot (S m) = (S m) * Tot m + m!`

(each of the `S m` choices of the new coordinate preserves the earlier records,
and exactly one of them is a new record), which in `QArith` is
`E[R_n] = E[R_{n-1}] + 1/n`, hence `H_n`. This is the compositional
average-case discipline (`framework/Expect.v`) applied to an exponential outcome
space without enumerating it.

## Program grounding + framework reuse

`Records.v` models permutations by rank vectors. The companion
[`targets/rocq/RecordsProgram.v`](targets/rocq/RecordsProgram.v) (axiom-free)
grounds the SAME `H_n` in an **instrumented program over actual permutations** and
**reuses the shared library** `framework/Permutations.v` (`Require Import Permutations`):

- `records` — an operational left-to-right-maxima counter (`records_op`).
- `records_op_sum` — value `v` is a left-to-right maximum of `s` iff it precedes
  every larger value, i.e. `v = firstSel(≥v) s`. This recasts the program as the
  library's `Pfirst`, so the counting reduces to the framework's
  **`count_first_value`** — no bespoke combinatorics in this unit.
- `records_program_expected` — `expect_records n == harmonic n`, where
  `expect_records n = (Σ over perms of records)/n!`. `H_n` falls straight out:
  `v` is first among the `n−v` values `≥ v` with probability `1/(n−v)`, so
  `E = Σ_{v<n} 1/(n−v) = H_n`.

This is the framework paying off — a second classic average proved by reusing one
lemma (`count_first_value`), the same lemma behind quicksort's `compared_count`.

## Cost model
`func-ops`. Reference Rocq proofs (axiom-free): the rank-vector model
`records_expected` in [`targets/rocq/Records.v`](targets/rocq/Records.v); the
program-grounded, framework-reusing `records_program_expected` in
[`targets/rocq/RecordsProgram.v`](targets/rocq/RecordsProgram.v).
