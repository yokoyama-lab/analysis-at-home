# XOR swap — exchange with no temporary

## Claim
The three-XOR trick `a ^= b; b ^= a; a ^= b`, captured as `xorswap`, swaps:

> **`xorswap_correct`**: `xorswap a b = (b, a)`.

## Proof idea
Purely from XOR being commutative, associative and self-cancelling
(`x XOR x = 0`, `0 XOR x = x`).

## Cost model
`func-ops`. Reference Rocq proof (`xorswap_correct`, axiom-free):
[`targets/rocq/XorSwap.v`](targets/rocq/XorSwap.v).
