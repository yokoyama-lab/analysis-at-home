# Run-length encoding — lossless round-trip

## Claim
`encode` collapses maximal runs into `(value, count)` pairs; `decode` expands
them with `repeat`. Then

> **`rle_roundtrip`**: `decode (encode l) = l`.

Decoding the encoding recovers the original list exactly — the defining property
of a lossless compressor.

## Proof idea
Induction on the list, casing on the head pair of `encode xs`: either the new
element extends the leading run (`S c`) or starts a fresh one.

## Cost model
`func-ops`. Reference Rocq proof (`rle_roundtrip`, axiom-free):
[`targets/rocq/RLE.v`](targets/rocq/RLE.v).
