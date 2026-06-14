# Euclid's algorithm (TAOCP Algorithm E)

> *The first algorithm in* The Art of Computer Programming *(Vol. 1 §1.1).*

## Claim
The fuel-bounded Euclidean algorithm `euclid fuel a b` returns `(gcd, #steps)` and:

1. **Cost** — `euclid_steps_le`: the number of division steps is at most `b`:
   > `snd (euclid fuel a b) <= b`.

   (Each step replaces `(a, b)` by `(b, a mod b)`, and `a mod b < b`, so the
   divisor strictly decreases — at most `b` steps.)

2. **Correctness** — `euclid_correct`: with enough fuel it computes the gcd:
   > `b <= fuel -> fst (euclid fuel a b) = Nat.gcd a b`.

The step bound here is the easy **linear** one. Knuth's **tight** bound is
`O(log b)`, with the worst case at consecutive Fibonacci numbers (**Lamé's
theorem**) — a harder future unit in this series.

## Cost model
`func-ops`, `counts = ["division"]`. Reference Rocq proof (`euclid_steps_le` and
`euclid_correct`, axiom-free):
[`targets/rocq/Euclid.v`](targets/rocq/Euclid.v).
