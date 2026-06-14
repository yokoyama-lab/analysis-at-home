# Karatsuba uses 3^k multiplications (n^lg3)

## Claim
Karatsuba's algorithm multiplies two 2n-digit numbers with **3** half-size
multiplications instead of the schoolbook 4. So the multiplication count `M` on
`2^k`-digit inputs obeys `M(S k) = 3*M(k)`, `M(0)=1`, giving
> `M k = 3 ^ k`.

Since `n = 2^k`, `3^k = (2^k)^{log_2 3} = n^{lg 3} ~ n^{1.585}` — sub-quadratic,
beating the `n^2` of `classical-multiplication`.

## Cost model
`func-ops`, `counts = ["multiplication"]`. Reference Rocq proof (`karatsuba_multiplications`, axiom-free):
[`targets/rocq/Karatsuba.v`](targets/rocq/Karatsuba.v).
