# TAOCP Algorithm M — running-maximum updates

> *Knuth's canonical example of average-case analysis (Vol. 1 §1.2.10).*

## Claim
Scanning a list left to right keeping a running maximum (Algorithm M's loop, with
its update step `k := j`), the number of updates `lr_changes cur l` against an
initial maximum `cur` is at most the list length:
> `lr_changes cur l <= length l`.

The bound is **tight**: a strictly increasing input (seeded below it) updates the
maximum on every element.

## Worst / average / best
- **Worst case** (this unit, kernel-verified): `≤ length l`, attained by increasing input.
- **Best case**: `0`, when the first element is the maximum.
- **Average** (conjecture track): over a uniformly random permutation the expected
  number of updates is `H_n − 1`, i.e. the number of left-to-right maxima is the
  harmonic number `H_n = Σ_{i=1}^n 1/i`. See
  [`tools/conjecture/results/algorithm-m-maxima.json`](../../tools/conjecture/results/algorithm-m-maxima.json).
  This harmonic average is a natural **future kernel twin** — we already verify
  harmonic numbers in [`quicksort-average-comparisons`](../quicksort-average-comparisons/).

## Cost model
`func-ops`, `counts = ["max-update"]`. Reference Rocq proof
(`algorithm_m_changes_le`, axiom-free):
[`targets/rocq/AlgorithmM.v`](targets/rocq/AlgorithmM.v).
