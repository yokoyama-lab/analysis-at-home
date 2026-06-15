# XOR single-number — the lone element in O(1) space

> A one-pass, no-extra-memory trick; the XOR cousin of
> [`boyer-moore-majority`](../boyer-moore-majority/).

## Claim
Let `xorsum = fold_right Nat.lxor 0`. If a list is any ordering of `m` together
with a list duplicated (`d ++ d`), then

> **`single_number`**: `Permutation l (m :: d ++ d) -> xorsum l = m`.

XOR-ing the whole list — one pass, a single accumulator — leaves exactly the
element that has no partner. No sorting, no hash set.

## Proof idea
Two properties of bitwise XOR:

- **order-independence** (`xorsum_perm`): XOR is commutative and associative, so
  the fold is invariant under any permutation of the list;
- **self-cancellation** (`xorsum_dup`): `xorsum (d ++ d) = 0` because
  `x XOR x = 0`.

Then `xorsum l = xorsum (m :: d ++ d) = m XOR 0 = m`.

## Cost model
`func-ops`, `counts = ["xor"]`. Reference Rocq proof (`single_number`,
axiom-free): [`targets/rocq/XorSingle.v`](targets/rocq/XorSingle.v).
