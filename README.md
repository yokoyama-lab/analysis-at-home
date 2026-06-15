# analysis@home

**Spare AI, turned into proven math.**

Point your LLM at an open problem. Get back a proof the kernel actually checked.
No trust required.

> Folding@home for proofs.

**🌐 Live board: <https://yokoyama-lab.github.io/analysis-at-home/>** — the
verification matrix, open jobs to claim, and the conjecture track (computed cost
distributions & limits).

---

## What this is

analysis@home turns spare LLM capacity into **machine-checked mathematics about
algorithms** — not just _"it works"_, but _"it runs in O(n log n)"_, proven by a
proof-assistant kernel.

Contributors run their **own** LLM (Claude, or anything else) against open *work
units* — an unproven complexity bound, a conjectured closed form, an algorithm
still waiting for its correctness proof — and submit candidate proofs. The
project re-checks every submission with a proof-assistant kernel
(**Rocq / Lean / Agda / Isabelle**) and keeps only what holds.

Because every contribution is **verified rather than trusted**, a corpus of
certified correctness and cost bounds grows from many hands — without anyone
having to trust the hands.

## How it works

**1 — Grab a work unit.**
An unproven complexity bound. A conjectured closed form. An algorithm still
waiting for its correctness proof.

**2 — Run your own LLM on it.**
Your machine, your account, your spare capacity. **Credentials never leave your
laptop.** The translation of an informal statement into a specific kernel
(Rocq / Lean / Agda / Isabelle) is itself a work unit an LLM can do — so the human load is
near zero.

**3 — Submit.**
The kernel re-checks every line. If it holds, it lands in the corpus —
permanently, and provably.

## Why it's different

- 🔒 **Verified, not trusted.** We don't care who — or what — wrote the proof.
  The kernel does the believing, so anyone can contribute and nobody has to be
  trusted. The server **never** calls an LLM and **never** stores your
  credentials.
- 📈 **Correctness _and_ cost.** Machine-checked complexity, not just
  functional correctness — the part competition-math-focused LLM-proof projects
  skip. And cost across the full picture: **worst-case, best-case, and average
  (expected) cost**, plus the **cost distribution** and its **limiting law**.
- 🌐 **Bring your own LLM.** We coordinate the work and re-verify the results.
  Your unused capacity stops going to waste.

## Verified average-case cost — a reusable library, kept honest by an oracle

Worst-case complexity has been mechanized before (CFML time credits, Guéneau's
big-O, McCarthy's running-time monad); **average-case** (expected) cost is
comparatively unformalized, and what exists (Eberl's Isabelle/AFP work) is largely
bespoke per algorithm. Our angle is a **small, reused Rocq library** for expected
cost, plus a **computation oracle** that checks the *statement* before anyone
proves it.

- **A shared average-case library.** `framework/Permutations.v` (axiom-free) proves
  the permutation-enumeration core — `perms_correct`, `length_perms` (`= n!`),
  `NoDup_perms` — and the general counting lemma `count_first_value` (the first
  element of a subset of a uniform permutation is uniform, via an explicit
  transposition bijection). **Two different results reuse the same lemma:**
  quicksort's `compared_count` and records' `records_program_expected`.
- **Quicksort, end to end, from a real program.** The average comparison count
  `2(n+1)Hₙ − 4n` is kernel-checked (axiom-free) from an *instrumented* head-pivot
  counter — not just a recurrence: `cmp` → `cmp_eq_pairsum` (a comparison is a
  compared *pair*) → `compared_count` (a pair at interval distance `d` is compared
  in `2·n!/d` permutations) → `quicksort_pairsum_closed` (the sum **is** the closed
  form). See `work-units/quicksort-average-comparisons/`.
- **A deterministic computation oracle for faithfulness.** A wrong or weakened
  cost *statement* survives a kernel proof (the theorem of that name is still
  true). `tools/oracle_check.py` checks each formal mean `p/q` against the
  *exactly enumerated* `E[cost]` for small `n`, and `tools/fault_corpus.py`
  evaluates it: **12/12 plausible-but-wrong closed forms are caught** (e.g. the
  `Hₙ − 1` maxima-updates trap), faithful rewrites pass, and the one
  enumeration-window blind spot is reported, not hidden. Exact enumeration, not
  random sampling — see [`docs/oracle-evaluation.md`](docs/oracle-evaluation.md).

A unit may `Require Import` the framework: the verifier precompiles `framework/*.v`
(from source, still kernel-checked end to end), so contributors build *on* the
library instead of re-deriving it.

## The two-track pipeline

| Track | Tooling | Output |
|-------|---------|--------|
| **Conjecture** | pure-Python computer algebra + exhaustive enumeration: exact cost distributions, closed-form guessing (finite differences), limit-law fitting | _candidate_ closed forms, distributions & limit laws (fast, **unproven**) |
| **Verify** | Rocq / Lean / Agda / Isabelle kernel (cost via time-credit style reasoning) | **theorems** |

A claim is only called *proven* once it has passed the verify track. The
conjecture track is a hypothesis generator, never the final word: it *computes*
`E[cost(n)]` and the limiting distribution, and the verify track promotes the
provable part (the exact mean) to a kernel-checked theorem. For example, for
linear search the conjecture track computes `E[cost] = (n+1)/2` with a **Uniform**
limit, and `linear-search-average-comparisons` proves the mean exactly; for
insertion sort, the inversion count is **Gaussian** in the limit with mean
`n(n−1)/4`.

For closed-form **sums** the bridge is tighter still: computer algebra
(Gosper / Zeilberger / WZ) emits both the closed form **and** a *telescoping
certificate* `F(k+1) − F(k) = a(k)` that the kernel re-checks by a one-line
induction — see `geometric-weighted-sum` (`Σ k·2^k`). The conjecture solver is
pure stdlib (`tools/conjecture/conjecture.py`); `tools/conjecture/cas_explore.py`
adds an optional sympy cross-check and solves the quicksort-average recurrence,
whose closed form `2(n+1)Hₙ − 4n` is itself kernel-checked in QArith by
`quicksort-average-comparisons` (rationals + harmonic numbers).

## Status

🛠️ **Phase 1 — the vertical slice works locally.** The worst-case
**comparison count of insertion sort** is proved and kernel-checked (axiom-free)
under two cost models — functional (`func-ops`) and imperative WHILE
(`while-ops`). The coordinator serves the web MVP, accepts a pasted proof, and
the verifier re-checks it with the Rocq kernel (`Print Assumptions` ⇒ "closed
under the global context"). Run it: `npm --prefix coordinator install && npm
--prefix coordinator start`.

Remaining before public exposure: signature-equivalence, a sandbox, and
persistence — see [`docs/roadmap.md`](docs/roadmap.md).

## Layout

```
docs/         design notes, work-unit format, roadmap, research plan + oracle eval
framework/    reusable average-case library (Permutations.v: count_first_value, …)
work-units/   the open problems + per-backend statements (seed: insertion sort)
tools/        conjecture solver, oracle_check.py, fault_corpus.py, board, verify
verifier/     pluggable kernel adapters (Rocq / Lean / Agda / Isabelle) — the trust anchor
coordinator/  dispatch work units, accept submissions, record verified status
web/          minimal "paste prompt → paste proof back" MVP, no auth
```

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md). Verified contributors are credited in
the corpus and on the leaderboard — a non-monetary, non-transferable
reputation (deliberately: see [`docs/design.md`](docs/design.md) on why we avoid
token rewards).

## License

- **Code:** Apache-2.0 (see [`LICENSE`](LICENSE)).
- **Proof corpus / work units:** CC-BY-4.0 (planned; see `docs/design.md`).
