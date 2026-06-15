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

## Cost model
`func-ops`. Reference Rocq proof (`records_expected`, axiom-free):
[`targets/rocq/Records.v`](targets/rocq/Records.v).
