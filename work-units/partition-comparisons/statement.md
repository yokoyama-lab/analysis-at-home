# Partitioning n elements uses n comparisons

## Claim
> `snd (partitionc piv l) = length l`.

The quicksort partition step compares each element to the pivot once.

## Cost model
Reference Rocq proof (`partition_comparisons`, axiom-free): [`targets/rocq/Partition.v`](targets/rocq/Partition.v).
