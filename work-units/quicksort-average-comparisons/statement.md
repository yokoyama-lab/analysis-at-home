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

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof
(`quicksort_average_closed_form`, axiom-free):
[`targets/rocq/QuicksortAverage.v`](targets/rocq/QuicksortAverage.v).
