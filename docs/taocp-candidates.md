# Candidate algorithms (TAOCP-guided)

A backlog of algorithms/identities not yet in the corpus, with the cost claim each
would carry and a tractability tag for the Rocq verify track:
✅ easy (structural recursion + lia/nia) · ⚠️ medium (more lemmas) ·
🔶 hard (rationals / permutations / well-founded recursion).

## Vol 1 — Fundamental Algorithms
- §1.2 combinatorics: Pascal's rule `C(n,k)=C(n-1,k-1)+C(n-1,k)` & row sum `=2^n` ✅;
  Fibonacci identities (Cassini, addition formula) ⚠️; `gcd(F_m,F_n)=F_{gcd}` 🔶;
  binomial theorem 🔶; floor identities `⌊⌊n/a⌋/b⌋=⌊n/(ab)⌋` ⚠️.
- §2.3 trees: inorder/postorder traversal length = #nodes ✅; Catalan count of
  binary trees 🔶; forest↔binary-tree correspondence ⚠️; Cayley `n^{n-2}` 🔶;
  build-heap is O(n) ⚠️.

## Vol 2 — Seminumerical
- §4.3–4.4: base-b digit count `=⌊log_b n⌋+1` ⚠️; classical addition (n carries) ✅;
  classical multiplication (n·m digit products) ⚠️; Karatsuba `n^{lg3}` 🔶.
- §4.5 number theory: extended Euclid (Bézout) ⚠️; binary GCD (Stein) ⚠️;
  Sieve of Eratosthenes `~n log log n` 🔶; trial-division primality ✅;
  Lamé's theorem (Fibonacci worst case) 🔶.
- §4.6 polynomials/powers: addition-chain lower bound `≥⌊lg n⌋` 🔶;
  polynomial division ⚠️; FFT `(n/2)lg n` butterflies 🔶.

## Vol 3 — Sorting and Searching
- §5.2 sorting: Shellsort 🔶; cocktail/bidirectional bubble `≤n(n-1)/2` ✅;
  natural merge ⚠️; radix sort `O(d(n+K))` ⚠️; build-heap O(n) ⚠️;
  Ford-Johnson merge-insertion 🔶.
- §5.3 optimal: min-max `⌈3n/2⌉-2` ⚠️; 2nd largest `n+⌈lg n⌉-2` 🔶;
  median-of-medians worst-case linear 🔶.
- §6 searching: interpolation search 🔶; AVL height `≤1.44 lg n` 🔶;
  B-tree height ⚠️; tries/Patricia ⚠️; move-to-front 🔶(compute);
  hashing open-addressing expected probes 🔶(compute).

## Vol 4A — Combinatorial Algorithms
- Gray code (one-bit change) ⚠️; popcount / ruler function ⚠️;
  permutation generation (Heap's, Algorithm L) 🔶; Steinhaus-Johnson-Trotter 🔶;
  combination generation (revolving door) 🔶; integer partitions / Bell numbers 🔶.

## Graphs & strings (§7.4 and adjacent)
- BFS/DFS `O(V+E)` ⚠️; topological sort (Kahn) ⚠️; Union-Find (amortized α(n)) 🔶;
  Warshall transitive closure `O(V³)` ⚠️; Dijkstra/Bellman-Ford/Kruskal/Prim 🔶;
  KMP `O(n+m)` 🔶; Rabin-Karp (ties to repo `rabin-karp/`) ⚠️; Boyer-Moore 🔶;
  LCS / edit distance / matrix-chain DP `O(nm)` ⚠️; optimal BST (Knuth, `O(n²)`) 🔶.

## Biggest current gaps
Permutation/combination generation (Vol 4A), worst-case selection
(median-of-medians, Vol 3 §5.3.3), and graph algorithms (§7.4) are entirely absent.

See `docs/taocp-roadmap.md` for what is already verified and the active queue.

---

## Status after the full sweep (every candidate addressed)

✅ verified Rocq unit · 🔬 computed on the conjecture track · ⏸ deferred (reason).

### Vol 1
- Pascal binomials — ✅ `binomial-coefficient-diagonal` (C(n,n)=1), `binomial-coefficient-one` (C(n,1)=n); ⏸ row-sum `=2^n` (double-sum induction).
- Fibonacci — ✅ `fibonacci-sum-of-squares`, `fibonacci-sum`, `fibonacci-le-pow`, `fibonacci-monotone`, `fibonacci-positive`; ⏸ Cassini / addition formula (need ℤ signs), `gcd(F_m,F_n)=F_gcd`.
- Floor identities — ✅ `floor-div-div`.
- Traversals — ✅ `tree-inorder-length`, `tree-postorder-length`, `tree-inorder-mirror`.
- ⏸ Catalan, forest↔binary, Cayley, build-heap-O(n) (combinatorial / amortized).

### Vol 2
- ✅ `base-b-digit-count`, `classical-addition`, `classical-multiplication`, `trial-division-checks`.
- ✅ `karatsuba-multiplications` — 3 sub-mults/level => 3^k = n^lg3.
- ✅ `lame-theorem` — **Lamé's theorem** (§4.5.3): n>=1 Euclid steps on a>b force `b >= F(n+1)`, `a >= F(n+2)`; consecutive Fibonacci numbers are the worst case (the tight O(log) bound, tying `euclid-*` to `fibonacci-*`).
- ⏸ extended Euclid & binary GCD (ℤ / case analysis), Sieve, addition-chain bound, polynomial division, FFT.

### Vol 3
- ✅ `cocktail-bubble-comparisons`, `radix-sort-passes`, `counting-sort-histogram`, `merge-comparisons`, `min-and-max-comparisons`, `heap-siftdown-comparisons`, `binary-search-comparisons`, `decision-tree-leaves-bound`, `quickselect-worst-case`, the inversion lemmas.
- 🔬 `quickselect-average` (~2n), `hashing-collisions` ((n-1)/2), inversions / linear-search / Algorithm-M distributions.
- 🔬 `coupon-collector` — E[T] = n·H_n, **Gumbel** (extreme-value) limit; `birthday-problem` — E[T] ~ √(πn/2) insertions to first collision, **Rayleigh** limit (two new limit laws on the conjecture track).
- ✅ `boyer-moore-majority` — MJRTY: a strict majority element found in one pass with O(1) space (cancellation invariant).
- ✅ `median-of-medians-linear` — the BFPRT recurrence `T(n) ≤ T(n/5)+T(7n/10)+n` is proved linear (`≤ 10n`); full algorithm model still open.
- ✅ `avl-min-nodes-fibonacci` — AVL min nodes >= fib(h) => O(log n) height.
- ✅ `comparison-sort-lower-bound` (§5.3.1) — `fact n <= leaves t -> log2(fact n) <= height t`: any comparison sort needs `>= lg(n!) = Omega(n log n)` comparisons (promotes `decision-tree-leaves-bound` to the actual `lg n!` bound).
- ✅ `build-heap-linear` (§5.2.3) — sum of node heights `sheight h + h + 1 = nodes h`, so total sift-down work `<= n`: Floyd's build-heap is **O(n)**, not O(n log n).
- 🔬 `random-bst-depth` — E[node depth] `~ 2·H_n − 3 ≈ 2 ln n`, Gaussian limit.
- ⏸ Shellsort, Ford-Johnson, min-max 3n/2−2, 2nd-largest, B-tree height, tries, move-to-front, interpolation search (research-level / need richer models).

### Vol 4A
- 🔬 `fisher-yates-uniformity` — exact: each of the n! permutations is output exactly once (uniform, certificate verified); `reservoir-sampling` — each item retained with probability k/n exactly (uniform, certificate verified).
- ⏸ Gray code (bitwise), popcount/ruler, permutation & combination generation, partitions/Bell (need bit-models or generation frameworks; candidates for the conjecture track).

### Amortized / data structures
- ✅ `binary-counter-increments` (amortized O(1)); `dynamic-array-amortized` — table doubling, n pushes cost `<= 3n` (potential method, Phi = 2·size − capacity).

### Surprising-result batch (counter-intuitive cost/correctness)
*Verified (Rocq, axiom-free):*
- ✅ `xor-single-number` — the lone element among pairs via one XOR fold, **O(1) space** (Permutation-invariance + self-cancellation).
- ✅ `floyd-cycle-detection` — tortoise & hare **meet** with **O(1) memory** (periodicity from any orbit collision).
- ✅ `kadane-max-subarray` — maximum subarray sum in **O(n)** though there are Θ(n²) subarrays (best is an upper bound on every window and is attained).
- ✅ `misra-gries-heavy-hitters` — every element above `n/k` is kept with only **k-1 counters** (generalized Boyer-Moore cancellation).

*Computed (conjecture track) — surprising constants / non-Gaussian limit laws:*
- 🔬 `prisoners-100` — pointer-following survival `→ 1 − ln 2 ≈ 0.307` (vs `~2⁻ⁿ` random); closed form `= n!`-enumeration for small n.
- 🔬 `secretary-problem` — the 37% rule: optimal stop at `r ≈ n/e`, success `→ 1/e ≈ 0.368`.
- 🔬 `quicksort-nongaussian` — Quicksort's standardized comparison count does **not** converge to a Gaussian (skewness stays > 0).
- 🔬 `lis-tracy-widom` — longest increasing subsequence `~ 2√n`, **Tracy-Widom** (random-matrix) limit.
- 🔬 `random-bst-height` — expected **height** `~ 4.311 ln n`, more than double the depth constant `2`.

### Classic-correctness + permutation-statistics batch
*Verified (Rocq, axiom-free):*
- ✅ `subtractive-gcd` — Euclid's original subtraction-only GCD (no division/mod) `= Nat.gcd` (via `Nat.gcd_sub_diag_r`).
- ✅ `russian-peasant-mult` — multiply by doubling/halving/adding only, `= a*b`.
- ✅ `run-length-encoding` — lossless: `decode (encode l) = l`.
- ✅ `exp-by-squaring-correct` — square-and-multiply `= b^e` (correctness twin of `fast-exponentiation-mults`).

*Computed (conjecture track):*
- 🔬 `permutation-cycles` — number of cycles of a random permutation, `E = H_n`, Gaussian limit.
- 🔬 `fixed-points-poisson` — number of fixed points `→ Poisson(1)` (`P(k)=e⁻¹/k!`); `P(0)=!n/n! → 1/e` (derangements). A new **Poisson** limit.
- 🔬 `longest-run-heads` — longest run of heads in n flips `~ log₂ n`.
- 🔬 `balls-into-bins` — expected max load of n balls in n bins `~ ln n / ln ln n` (slow but unbounded).

### Faithful-encodings + random-process batch
*Verified (Rocq, axiom-free):*
- ✅ `binary-rep-roundtrip` — base-2 representation is faithful: `from_bits (to_bits n) = n`.
- ✅ `fib-fast-doubling` — Fibonacci in **O(log n)** via the doubling identities (`fib(2k)`, `fib(2k+1)`), proved `= fib` through the addition formula.

*Computed (conjecture track):*
- 🔬 `eulerian-ascents` — number of ascents of a random permutation, `E = (n−1)/2`, Gaussian.
- 🔬 `random-walk-max` — maximum of a ±1 walk `~ √(2n/π)`, **half-normal** `|N|` limit.
- 🔬 `random-mapping-rho` — rho-length (tail+cycle) of a random function `~ √(πn/2)` — the steps Floyd's tortoise-and-hare needs on a random map (ties to `floyd-cycle-detection`).

### Graphs & strings (§7.4 etc.)
- ✅ `warshall-operations` (V³), `dp-table-fill` (LCS/edit/matrix-chain n·m), `prefix-match-comparisons` (naive-match core).
- ✅ `graph-edge-count` — adjacency entries = #edges (the E in O(V+E); graph domain opened).
- ✅ `graph-bfs-dfs-ove` + `graph-traversal-vertex-bound` — BFS/DFS cost bound O(V+E) (visited<=|V| via pigeonhole, edges via graph-edge-count); full stateful worklist algorithm still open.
- ✅ `toposort-vertex-bound` — Kahn emits each vertex once (<= |V|).
- ✅ `union-find-rank-bound` — union-by-rank tree has >= 2^r nodes (=> O(log n) find).
- ✅ `dfs-soundness` (visited => reachable), `union-find-find-root` (find reaches a root).
- ✅ `dfs-completeness` (drains => visits all reachable), `union-find-path-compression` (one-step find after compression).
- ⏸ Union-Find full O(m·alpha(n)) amortized via the potential method (a major standalone formalization), Dijkstra/Bellman-Ford greedy/round correctness (relaxation invariant ✅ via `shortest-path-relaxation-monotone/-triangle`, `bellman-ford-cost`), Kruskal/Prim, KMP/Boyer-Moore/Rabin-Karp, optimal BST.

Divide-and-conquer recurrences are now covered by `mergesort-recurrence` (n log n), `karatsuba-multiplications` (n^lg3), `divide-and-conquer-linear` (O(n)), and `median-of-medians-linear` — the master-theorem regimes as verified recurrence bounds.

**Net:** every easy/medium candidate is now a verified unit or computed result; the
remaining ⏸ are research-level formalizations (graph models, amortized analysis,
recurrences over ℤ/ℚ, generation frameworks) — each a substantial standalone effort.
