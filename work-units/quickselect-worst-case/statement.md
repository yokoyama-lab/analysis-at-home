# Quickselect worst case: n(n-1)/2 comparisons

## Claim
> `2 * qsel_worst n + n = n * n`.

Each partition step costs n-1 comparisons and, with an extreme pivot, recurses on n-1 elements — giving the worst-case total n(n-1)/2 (stated as 2·cost + n = n²). The **average** case is linear (E[comparisons] = O(n)); proving that is a harder future unit (a quicksort-style recurrence with harmonic terms).

## Cost model
Reference Rocq proof (`quickselect_worst_case`, axiom-free): [`targets/rocq/Quickselect.v`](targets/rocq/Quickselect.v).
