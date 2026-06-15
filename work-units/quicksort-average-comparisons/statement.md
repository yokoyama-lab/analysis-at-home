# Average (expected) comparison count of randomized quicksort

## Claim
For a uniformly random permutation (equivalently, a random pivot), the expected
key-comparison count `C(n)` of quicksort satisfies the recurrence
> `C(n) = (n−1) + (2/n)·Σ_{k=0}^{n−1} C(k)`,  `C(0) = 0`,

which reduces to the first-order recurrence
> `n·C(n) = (n+1)·C(n−1) + 2(n−1)`,

and its **closed form** is
> `C(n) = 2(n+1)·H_n − 4n`,   where `H_n = Σ_{i=1}^n 1/i` is the n-th harmonic number.

(So `C(n) = Θ(n log n)`.) Small values: `C(2)=1`, `C(3)=8/3`, `C(4)=29/6`.

## The conjecture → kernel bridge
This is the **verify-track twin** of
[`tools/conjecture/results/quicksort-average.json`](../../tools/conjecture/results/quicksort-average.json),
produced by computer algebra in
[`tools/conjecture/cas_explore.py`](../../tools/conjecture/cas_explore.py): sympy
reduces the full-history recurrence and verifies that `2(n+1)H_n − 4n` satisfies
it (residual `= 0`). That residual identity is the **certificate**. Here the
kernel re-checks it: in `QArith` we define the harmonic number `H`, the recurrence
solution `C`, and the closed form `Cf`, and prove `C n == Cf n` — the induction
step is exactly the certificate, discharged by `field`.

This is the hardest of the average-case units: it genuinely needs **rationals and
harmonic numbers**, beyond the polynomial closed forms.

## Program grounding (not just a recurrence)

`QuicksortAverage.v` proves a *recurrence solution* equals the closed form — but a
recurrence is not a program, and "the cost is a combinatorial proxy" is the first
thing a referee attacks. [`targets/rocq/Quicksort.v`](targets/rocq/Quicksort.v)
(axiom-free) closes that gap with an **instrumented head-pivot comparison counter**
`cmp` on actual lists:

- **`cmp_cons`** — `cmp (p::xs) = |xs| + cmp (xs<p) + cmp (xs>p)`: `cmp` really is
  the partition-and-recurse comparison count.
- **computational tie** — summed over *every* permutation of `{0..n−1}`, `cmp`
  reproduces the closed form's small values: `Tot 2..6 = 2, 16, 116, 888, 7416`
  `= mean·n!` (matches the artifact's `small_values`), by `vm_compute`.
- **`cmp_eq_pairsum`** — the **pair-decomposition identity**: `cmp l` equals the
  number of element pairs that ever get *directly compared*, where a pair is
  compared iff, among the elements whose value lies in their closed interval, the
  first one in the input is one of the two. This is exactly
  `E[C] = Σ_{i<j} P[i,j compared]` (linearity of expectation) expressed at the
  **program level**, proved by structural case analysis on the pivot — no
  probability monad, no enumeration of the `n!` inputs.

**Stage 2 — from the pair decomposition to the closed form.** Grouping pairs by
interval distance `d = j−i+1` (there are `n+1−d` value-pairs at distance `d`):
`E[C] = Σ_{i<j} 2/(j−i+1) = 2·Σ_{d=2}^{n}(n+1−d)/d = 2(n+1)H_n − 4n`.

- **Part A (done, axiom-free)** —
  [`targets/rocq/QuicksortPairSum.v`](targets/rocq/QuicksortPairSum.v):
  `quicksort_pairsum_closed : 1≤n → 2·Σ_{d=2}^{n}(n+1−d)/d == 2(n+1)H_n − 4n`,
  in QArith. The arithmetic backbone of the linearity-of-expectation derivation.
- **Part B (done, axiom-free)** —
  [`framework/Permutations.v`](../../framework/Permutations.v):
  `compared_count : a < b → b < n → (b−a+1)·num_compared a b n = 2·n!`
  (division-free `d·count = 2·n!`). A fixed value-pair at interval distance `d` is
  compared in exactly `2·n!/d` of the `n!` permutations. This is the "first element
  of a subset of a uniform permutation is uniform" fact — free in a measure-theoretic
  setting (Eberl's Giry monad), proved here as an **explicit transposition bijection**
  over the permutation model: the reusable infrastructure `perms_correct`
  (`In p (perms L) ↔ Permutation L p`), `length_perms` (`= n!`), `NoDup_perms`, and
  the general `count_first_value`. `Quicksort.v`'s `vm_compute` checks remain as
  independent small-n sanity.

**With Parts A and B both proved, the chain is complete and kernel-checked end to
end:** instrumented program `cmp` → `cmp_eq_pairsum` (pairs) → `compared_count`
(`2·n!/d` per pair) → `quicksort_pairsum_closed` (`Σ` = closed form) → `2(n+1)H_n − 4n`.

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proofs (axiom-free): the
closed form `quicksort_average_closed_form` in
[`targets/rocq/QuicksortAverage.v`](targets/rocq/QuicksortAverage.v); the
program-grounded pair decomposition `cmp_eq_pairsum` in
[`targets/rocq/Quicksort.v`](targets/rocq/Quicksort.v). The mean `2(n+1)H_n − 4n`
is oracle-checked against the enumerated means (`tools/oracle_check.py`).
