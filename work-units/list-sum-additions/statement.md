# Summing n numbers uses n−1 additions

## Claim
Adding the `n` numbers in a list takes exactly **`n − 1`** additions:
> `snd (sum_list l) = pred (length l)`.

The instrumented summation folds the tail into an accumulator seeded with the
head, counting one addition per folded element — so the head costs nothing and an
`n`-element list costs `n − 1`.

A fundamental lower-bound-tight fact: combining `n` values with a binary operation
needs at least (and here exactly) `n − 1` operations.

## Cost model
`func-ops`, `counts = ["addition"]`. Reference Rocq proof (`list_sum_additions`,
axiom-free): [`targets/rocq/ListSum.v`](targets/rocq/ListSum.v).
