<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that **Floyd's
build-heap is O(n)** (TAOCP Vol. 3 §5.2.3). Mirror
`work-units/build-heap-linear/targets/rocq/BuildHeap.v`:

1. define `nodes h` (= 2^(h+1)-1) and `sheight h` (sum of node heights),
   with `sheight (S h') = S h' + 2 * sheight h'`;
2. prove `build_heap_identity`: `sheight h + h + 1 = nodes h`, hence
   `sheight h <= nodes h`.

The canonical theorem to certify is `build_heap_identity`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
