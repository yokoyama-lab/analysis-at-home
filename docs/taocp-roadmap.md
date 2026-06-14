# TAOCP proof series

A running effort to prove, one by one, the cost claims of algorithms from Knuth's
*The Art of Computer Programming* — correctness and/or operation counts, across
worst / best / average / distribution / limit, kernel-checked.

Conventions: each row is a work unit under `work-units/`. ✅ = at least one kernel
verifies it; 🔬 = computed on the conjecture track (not trusted). "Twin" means a
conjecture-track result whose mean is (or could be) promoted to a theorem.

## Verified (TAOCP-associated)

| Algorithm | TAOCP | Unit | Claim |
|---|---|---|---|
| Euclid (Algorithm E) | Vol 1 §1.1, Vol 2 §4.5.2 | `euclid-gcd` | ✅ steps ≤ b; gcd correct |
| Finding the maximum (Algorithm M) | Vol 1 §1.2.10 | `algorithm-m-maxima` | ✅ worst-case updates ≤ n; 🔬 avg = Hₙ |
| Horner's rule | Vol 2 §4.6.4 | `horner-multiplications` | ✅ n multiplications |
| Right-to-left binary exponentiation | Vol 2 §4.6.3 | `fast-exponentiation-mults` | ✅ ≤ 2⌊lg e⌋ mults |
| Insertion sort | Vol 3 §5.2.1 | `insertion-sort-comparisons`, `-best-case` | ✅ worst ≤ n(n−1)/2, best ≥ n−1 |
| Selection sort | Vol 3 §5.2.3 | `selection-sort-comparisons` | ✅ n(n−1)/2 |
| Merge sort | Vol 3 §5.2.4 | `merge-sort-comparisons` | ✅ merge bound |
| Quicksort (average) | Vol 3 §5.2.2 | `quicksort-average-comparisons` | ✅ 2(n+1)Hₙ−4n (Rocq+Isabelle) |
| Sequential search | Vol 3 §6.1 | `linear-search-comparisons`, `-best-case`, `-average-comparisons` | ✅ worst n, best 1, avg (n+1)/2 |
| Tower of Hanoi | Vol 1 §1.1 (ex.) | `tower-of-hanoi-moves` | ✅ 2ⁿ−1 moves |
| Binary counter (amortized) | Vol 4A | `binary-counter-increments` | ✅ amortized O(1) |
| Binary tree search | Vol 3 §6.2.2 | `bst-search-comparisons` | ✅ comparisons ≤ height |
| Summing n numbers | Vol 1/2 (basic) | `list-sum-additions` | ✅ n−1 additions |

### Fundamentals corpus (100-unit milestone)

The repository now holds **100 verified work units**. Beyond the named TAOCP
algorithms above, a broad base of fundamentals is kernel-verified (Rocq): list
operation counts (product, fold, all/any, nth, take/drop, zip, dedup, index-of,
replicate, countp) and list correctness laws (map/append/rev length, rev
involutive, take++drop, map fusion, filter bound, append associativity); tree
facts (perfect-tree height/leaves/internal, leaves=internal+1, size
decomposition, height bounds, mirror involutive/leaf-preserving, preorder length,
tree map/fold, BST insert comparisons & size growth); sum identities (Gauss,
squares, cubes/Nicomachus, odds, evens, i(i+1), triangulars, geometric base 2/3,
Fibonacci sum & bound, sum-const); and number/power facts (n<2ⁿ, laws of exponents
a^(m+n), a^(m·n), (ab)ⁿ, a¹, 1ⁿ, factorial positivity/recurrence/n≤n!, even-or-odd,
div-mod identity, mod bound, repeated squaring).

### Easy-win batch (fundamentals, 20 units)

Structural cost counts and sum identities, all kernel-verified (Rocq):

- **Lists** — `list-reversal-operations` (n cons), `list-append-operations` (|l₁|),
  `list-map-operations` (n), `list-filter-tests` (n), `list-sum-additions` (n−1).
- **Trees** (Vol 1 §2.3) — `tree-leaves-internal` (leaves = internal+1),
  `perfect-tree-leaves` (2ʰ), `perfect-tree-internal` (2ʰ−1),
  `tree-height-le-nodes`, `tree-mirror-operations`, `bst-search-comparisons`.
- **Sorting/searching** (Vol 3) — `partition-comparisons` (n),
  `sequential-search-membership` (≤ n), `min-and-max-comparisons` (2n).
- **Sums** (Vol 1 §1.2.3) — `gauss-sum` (n(n+1)/2), `sum-of-squares`,
  `sum-first-n-odds` (n²), `geometric-sum-two` (2ⁿ−1), `nicomachus-cubes`.
- **Numbers** — `exp-dominates-linear` (n<2ⁿ), `consecutive-product-even`,
  `repeated-squaring-mults` (k mults for x^(2ᵏ)).

(Plus building blocks: `factorial-mults`, `iterative-fibonacci-additions`,
`count-occurrences-comparisons`, `list-minimum/maximum-comparisons`,
`naive-power-mults`, `ordered-insertion-comparisons`, and the summation unit
`geometric-weighted-sum`.)

### Search/sort gaps filled

The classic search/sort canon is now well covered. Recently added:
`binary-search-comparisons` (⌊lg n⌋+1, the array binary search, Vol 3 §6.2.1),
`heap-siftdown-comparisons` (≤ 2·height, the heapsort primitive, Vol 3 §5.2.3),
and the inversion theory behind bubble sort (Vol 3 §5.2.2):
`inversions-adjacent-swap` (one swap removes one inversion) +
`sorted-zero-inversions` (sorted ⇒ 0) — together the crux of "bubble exchanges =
inversions". `quickselect-worst-case` (n(n−1)/2, Vol 3 §5.3.3) covers FIND's worst case.

## Queued — next in the series

**Recently addressed (this round).** Comparison-sort lower bound: the
decision-tree core `leaves t ≤ 2^height t` is verified (`decision-tree-leaves-bound`)
— a height-h tree has ≤ 2^h leaves, so distinguishing n! orderings forces
h ≥ ⌈lg n!⌉. Counting/radix sort: the partition invariant `sumhist = length` is
verified (`counting-sort-histogram`, comparison-free & linear). Bubble: the
swap-anywhere lemma `inversions-swap-anywhere` is verified (each swap removes one
inversion at any position). Quickselect **average** and **hashing** expected
collisions are now computed on the conjecture track (E[quickselect] grows ~2n;
E[collisions at load 1] = (n−1)/2, exact).

| Algorithm | TAOCP | Why it's interesting |
|---|---|---|
| Bubble exchanges = inversions (full run) | Vol 3 §5.2.2 | assemble swap-anywhere + sorted-zero via a decreasing measure; needs a permutation/termination proof |
| Quickselect average — kernel twin | Vol 3 §5.3.3 | promote the computed ~2n to a theorem (QArith recurrence with harmonic terms) |
| ⌈lg n!⌉ exact lower bound | Vol 3 §5.3.1 | tie `decision-tree-leaves-bound` to n! permutation leaves |
| Radix sort (d passes) | Vol 3 §5.2.5 | iterate counting sort over d digit-passes; total O(d·(n+K)) |
| Hashing expected probes — kernel twin | Vol 3 §6.4 | promote computed collisions/probes to a theorem |
| Lamé's theorem (tight Euclid bound) | Vol 2 §4.5.3 | worst case = consecutive Fibonacci numbers; O(log) bound |
| Algorithm M average = Hₙ−1 | Vol 1 §1.2.10 | kernel twin of the conjecture (harmonic; we now have QArith harmonic) |
| Balanced-tree height ⇒ O(log n) | Vol 3 §6.2.1–6.2.3 | upgrade `bst-search-comparisons` corollary to ⌊lg n⌋+1 on balanced trees |
| Lexicographic permutations (Algorithm L) | Vol 4A §7.2.1.2 | amortized cost per permutation |
| Gray code generation | Vol 4A §7.2.1.1 | one bit change per step |
| Classical multiplication | Vol 2 §4.3.1 (Algorithm M) | n·m digit multiplications |

Suggestions and PRs welcome — pick a queued row, prove it in any of the four
kernels, open a PR (see [`CONTRIBUTING.md`](../CONTRIBUTING.md)).
