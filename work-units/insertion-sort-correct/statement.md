# Insertion sort — full correctness

> Correctness companion to [`insertion-sort-comparisons`](../insertion-sort-comparisons/)
> (the worst-case `n(n-1)/2` comparison count).

## Claim
`isort (x::t) = insert x (isort t)`. Then

> **`isort_correct`**: `Sorted (isort l) /\ Permutation (isort l) l`.

The output is sorted **and** a permutation of the input — nothing is lost,
duplicated, or invented.

## Proof idea
`insert_sorted` (Sorted l → Sorted (insert x l)), by induction on the sortedness
derivation, case-splitting on the head comparison; `insert_perm`
(`Permutation (insert x l) (x::l)`) via `perm_skip` + `perm_swap`. `isort_correct`
then follows by induction on the list.

## Cost model
`func-ops`. Reference Rocq proof (`isort_correct`, axiom-free):
[`targets/rocq/InsSort.v`](targets/rocq/InsSort.v).
