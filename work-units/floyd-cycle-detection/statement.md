# Floyd's tortoise-and-hare — cycle detection in O(1) memory

> *R. W. Floyd; cf. Knuth TAOCP Vol. 2 §3.1.* Find a cycle with two pointers and
> no visited set.

## Claim
Consider the orbit `x, f(x), f(f(x)), ...` (`iter f k x`). If it ever repeats a
value — `iter f i x = iter f j x` with `i < j`, which **must** happen by
pigeonhole whenever the reachable set is finite — then a fast/slow pointer pair
meets:

> **`floyd_meeting`**: `i < j -> iter f i x = iter f j x -> exists m, 1 <= m /\ iter f m x = iter f (2*m) x`.

The tortoise takes `m` steps, the hare `2m`; they land on the same value, using
only the two pointers — `O(1)` memory.

## Proof idea
From the collision the orbit is **periodic** with period `λ = j − i` from index
`i` on (`periodic`), hence periodic with every multiple of `λ` (`multiperiod`).
Pick `m = (i+1)·λ`: it is `≥ i` and a multiple of `λ`, so
`iter f (2m) x = iter f (m + m) x = iter f m x`.

## Cost model
`func-ops`, `counts = ["apply"]`. Reference Rocq proof (`floyd_meeting`,
axiom-free): [`targets/rocq/Floyd.v`](targets/rocq/Floyd.v).
