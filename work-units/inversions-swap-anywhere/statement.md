# Swapping any adjacent inverted pair removes one inversion

## Claim
> `b < a -> inv (pre ++ a :: b :: post) = S (inv (pre ++ b :: a :: post))`.

Generalizes `inversions-adjacent-swap` to a swap at **any** position (via additivity of the inversion count over list concatenation). This is the inductive step toward Knuth's full theorem that **bubble sort's total exchanges equal the number of inversions**: each of bubble's adjacent swaps removes exactly one inversion, and the sorted result has zero (`sorted-zero-inversions`).

## Cost model
Reference Rocq proof (`inversions_swap_anywhere`, axiom-free): [`targets/rocq/InvSwapAnywhere.v`](targets/rocq/InvSwapAnywhere.v).
