# A sorted list has zero inversions

## Claim
> `sorted l -> inv l = 0`.

The other half of `bubble sort exchanges = inversions`: the sorted result has zero inversions, so the total number of adjacent swaps equals the inversions of the input.

## Cost model
Reference Rocq proof (`sorted_zero_inversions`, axiom-free): [`targets/rocq/SortedInv.v`](targets/rocq/SortedInv.v).
