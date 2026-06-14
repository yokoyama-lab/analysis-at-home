# Finding min and max by scanning uses 2n comparisons

## Claim
> `snd (mmc mn mx l) = 2 * length l`.

Naive simultaneous min/max: two comparisons per element. Knuth's 3n/2 - 2 optimum (pairing elements) is a harder future unit.

## Cost model
Reference Rocq proof (`minmax_comparisons`, axiom-free): [`targets/rocq/MinMax.v`](targets/rocq/MinMax.v).
