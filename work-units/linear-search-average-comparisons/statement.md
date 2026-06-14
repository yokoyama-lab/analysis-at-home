# Average (expected) comparison count of linear search

## Claim
For a target that is **present** and **equally likely to be in any of the `n`
positions**, linear search performs on average
> `(n + 1) / 2` comparisons.

This is the **verify-track twin** of the conjecture-track result
[`tools/conjecture/results/linear-search.json`](../../tools/conjecture/results/linear-search.json),
which *computes* `E[comparisons(n)] = (n+1)/2` and a **Uniform** limit law. Here we
*prove* the exact mean, in two axiom-free pieces:

1. **Cost-model grounding** (`lsearch_at`): if the target first matches at 1-based
   position `p` (a prefix of `p−1` non-matches, then the target), linear search
   performs **exactly `p`** comparisons.
2. **Exact sum** (`linear_search_avg_total`): summing `p` over the `n` equally
   likely positions gives `sum_upto n`, and
   > `2 * sum_upto n = n * (n + 1)`,

   so the average is exactly `(n+1)/2` (stated without division to stay in `nat`).

## Two-track relationship
The **conjecture track** computes the distribution and guesses the closed form
(not trusted). The **verify track** (this unit) proves the closed form exactly via
the kernel. Only the provable consequence — the mean — is promoted; the *limit
law* (Uniform) remains a computed conjecture.

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof
(`linear_search_avg_total`, axiom-free):
[`targets/rocq/LinearSearchAverage.v`](targets/rocq/LinearSearchAverage.v).
