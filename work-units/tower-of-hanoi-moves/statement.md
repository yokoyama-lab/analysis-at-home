# Exact move count of the Tower of Hanoi

## Claim

Solving the Tower of Hanoi for `n` disks takes **exactly** `2^n − 1` moves.
Division/subtraction-free form:

> `hanoi_moves n + 1 = 2 ^ n`,

where `hanoi_moves 0 = 0` and `hanoi_moves (n+1) = 2·hanoi_moves n + 1`.

## Cost model

`func-ops`, `counts = ["move"]`. Reference Rocq proof (`hanoi_moves_closed`,
axiom-free): [`targets/rocq/TowerOfHanoi.v`](targets/rocq/TowerOfHanoi.v). An
**exact closed form** (an equality, not a bound) by a one-line induction.

## References
Classic recurrence.
