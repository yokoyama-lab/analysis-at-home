# Expected hash collisions = (n-1)/2

> The second deep average-case result (pairwise structure), verified twin of the
> enumerated [`hashing-collisions.json`](../../tools/conjecture/results/hashing-collisions.json).

## Claim
Throwing `n` keys into `n` slots uniformly (load 1), the expected number of
colliding pairs is `(n-1)/2`:

> **`collisions_expected`**: `0 < n -> 2 * Tot_coll n n = (n-1) * n^n`

(division-free: `2*Σ = (n-1)*|assignments|`, i.e. mean `(n-1)/2`).

## Method (no enumeration of the n^n assignments)
The assignment space is the product `{1..n}^k`. Appending the k-th key (uniform in
`{1..n}`) adds `count_eq v c` collisions, and `Σ_{v∈{1..n}} count_eq v c = |c|`
(each existing key is matched by exactly one slot value). Hence
`Tot_coll(S m) = n*Tot_coll m + m*n^m`, giving the subtraction-free identity
`2*n*Tot_coll n k + k*n^k = k*k*n^k` (= `C(k,2)/n`); at `k=n`, the mean is
`(n-1)/2`. Linearity over the last coordinate again — here the pairwise sum
collapses to the running multiplicity.

## Framework reuse (product-space library)

`Coll.v` is self-contained. The companion
[`targets/rocq/CollProgram.v`](targets/rocq/CollProgram.v) (axiom-free) proves the
SAME result by **reusing** the shared product-space library
[`framework/Products.v`](../../framework/Products.v) (`Require Import Products`):
the assignment generator `prods`, `length_prods` (`= n^k`), and the
**marginalization primitive** `sum_count_eq_length` — summing a slot-multiplicity
over all `n` slots collapses to `|c|`, exactly what turns the pairwise collision
sum into the running-multiplicity recurrence `Tot_coll(S m) = n·Tot_coll m + m·n^m`.
Only the collision-specific counter `coll` and the assembly stay in the unit.

This is the **product-space analogue** of records reusing `framework/Permutations.v`
(`count_first_value`): the framework now carries both a permutation library and a
product library for average-case cost.

## Cost model
`func-ops`. Reference Rocq proofs (axiom-free): the self-contained
`collisions_expected` in [`targets/rocq/Coll.v`](targets/rocq/Coll.v); the
framework-reusing `collisions_expected_reuse` in
[`targets/rocq/CollProgram.v`](targets/rocq/CollProgram.v).
