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
