# Linear recursion with linear work is quadratic

## Claim
> `T 0 = 0 -> (forall k, T (S k) = T k + S k) -> forall k, 2 * T k = k * (k + 1)`.

## Cost model
Reference Rocq proof (`linear_recursion_quadratic`, axiom-free): [`targets/rocq/LinRecQuad.v`](targets/rocq/LinRecQuad.v).
