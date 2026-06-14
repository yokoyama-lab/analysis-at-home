# Closed form of the weighted geometric sum Σ k·2^k

## Claim
> `Σ_{k=0}^{n-1} k·2^k = (n−2)·2^n + 2`,

stated in `nat` without subtraction as
> `wsum n + 2·2^n = n·2^n + 2`   where `wsum n = Σ_{k<n} k·2^k`.

`Σ k·2^k` is the total **depth-weighted work** in a binary recursion — `k` units of
work at each of the `2^k` nodes on level `k`.

## The Gosper/WZ bridge (conjecture → certificate → kernel)
This is the **verify-track twin** of
[`tools/conjecture/results/closed-form-sum-k2k.json`](../../tools/conjecture/results/closed-form-sum-k2k.json).
The conjecture track (`tools/conjecture/conjecture.py`, pure stdlib) finds the
closed form by a **Gosper-style antidifference**: it solves for `F` with
> `F(k+1) − F(k) = k·2^k`,   giving `F(k) = (k−2)·2^k`,

so `Σ_{k<n} k·2^k = F(n) − F(0) = (n−2)·2^n + 2`. The identity `F(k+1)−F(k)=k·2^k`
is a **telescoping certificate** — a one-line fact the kernel re-checks by a
routine induction (exactly the step in the Rocq proof). `tools/conjecture/cas_explore.py`
cross-checks the same antidifference with sympy/Gosper.

This is the general pattern: for hypergeometric sums, computer algebra
(Gosper / Zeilberger / WZ) emits both the closed form **and** a machine-checkable
certificate, so the verify-track proof reduces to confirming the certificate.

## Cost model
`func-ops`, `counts = ["operation"]`. Reference Rocq proof
(`geometric_weighted_sum`, axiom-free):
[`targets/rocq/GeometricWeightedSum.v`](targets/rocq/GeometricWeightedSum.v).
