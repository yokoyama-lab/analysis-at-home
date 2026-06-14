# Swapping an adjacent inverted pair removes one inversion

## Claim
> `b < a -> inv (a :: b :: l) = S (inv (b :: a :: l))`.

The heart of Knuth's theorem that **bubble sort's exchanges equal the number of inversions**: each adjacent swap of an out-of-order pair removes exactly one inversion. Combined with `sorted-zero-inversions`, this pins down the total exchange count.

## Cost model
Reference Rocq proof (`inversions_adjacent_swap`, axiom-free): [`targets/rocq/InvSwap.v`](targets/rocq/InvSwap.v).
