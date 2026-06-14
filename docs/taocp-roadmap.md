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

(Plus building blocks: `factorial-mults`, `iterative-fibonacci-additions`,
`count-occurrences-comparisons`, `list-minimum/maximum-comparisons`,
`naive-power-mults`, `ordered-insertion-comparisons`, and the summation unit
`geometric-weighted-sum`.)

## Queued — next in the series

| Algorithm | TAOCP | Why it's interesting |
|---|---|---|
| Lamé's theorem (tight Euclid bound) | Vol 2 §4.5.3 | worst case = consecutive Fibonacci numbers; O(log) bound |
| Algorithm M average = Hₙ−1 | Vol 1 §1.2.10 | kernel twin of the conjecture (harmonic; we now have QArith harmonic) |
| Binary search | Vol 3 §6.2.1 (Algorithm B) | ⌊lg n⌋+1 comparisons |
| Bubble sort exchanges = #inversions | Vol 3 §5.2.2 | ties to the inversions distribution (Gaussian, mean n(n−1)/4) |
| Distribution counting sort | Vol 3 §5.2 | exact linear operation count |
| Heapsort sift-up | Vol 3 §5.2.3 | ≤ ⌊lg n⌋ per sift |
| Quickselect / FIND (average) | Vol 3 §5.3.3 | linear expected, another harmonic-flavored average |
| Lexicographic permutations (Algorithm L) | Vol 4A §7.2.1.2 | amortized cost per permutation |
| Gray code generation | Vol 4A §7.2.1.1 | one bit change per step |
| Classical multiplication | Vol 2 §4.3.1 (Algorithm M) | n·m digit multiplications |

Suggestions and PRs welcome — pick a queued row, prove it in any of the four
kernels, open a PR (see [`CONTRIBUTING.md`](../CONTRIBUTING.md)).
