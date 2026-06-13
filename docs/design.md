# Design

## Goal

Build a crowdsourced, LLM-assisted system that produces **kernel-checked proofs
of algorithm correctness _and_ complexity / cost bounds**, and accumulates them
into a citable corpus.

## The one invariant that must never break

> **verified, not trusted.**

Concretely, this forces three hard rules on the architecture:

1. The **coordinator / server never calls an LLM.** All generation happens on
   contributors' own machines with their own accounts.
2. The server **never stores contributor credentials** (API keys, session
   tokens). It only ever sees *candidate proofs* (source text) and re-checks
   them.
3. **Verification is kernel-only.** A submission is accepted iff a proof
   assistant's trusted kernel (Rocq / Lean / Agda / Isabelle) accepts it. The LLM that
   produced it may be wrong, adversarial, or unknown — it does not matter.

This is also what makes the project **regulation- and ToS-clean**: each
contributor is simply using their own LLM normally, and the trust problem that
plagues volunteer computing (e.g. Folding@home credit-faking) is dissolved — a
forged proof simply fails the kernel.

## Why correctness *and* cost

LLM theorem-proving today is overwhelmingly aimed at **competition mathematics**
(miniF2F, ProofNet, …). The "correctness + computational complexity" of
algorithms — the part that took the literature decades of careful hand analysis
— is barely benchmarked. That gap is the project's research contribution:

- **Functional correctness**: e.g. "insertion sort returns a sorted permutation."
  Largely an extension of existing teaching material (Software Foundations /
  Verified Functional Algorithms).
- **Cost analysis**: e.g. "insertion sort uses ≤ n(n−1)/2 comparisons." The
  frontier. Targeted via time-credit / amortized-cost style reasoning
  (Charguéraud–Pottier and successors).

## Multiple backends, on purpose

Work units are **backend-agnostic**. A unit states an informal claim; producing
a `rocq` / `lean` / `agda` / `isabelle` rendition of it is itself a task that an LLM (or a
contributor) performs. Rationale:

- The informal → formal **translation is LLM-friendly**, so it imposes near-zero
  human load and is itself a dispatchable work unit.
- Trying several kernels is **free signal**: if a claim is provable in one and
  stubbornly resistant in another, that is itself interesting. "Couldn't be done
  in backend X" is an acceptable, informative outcome — not a failure.

The verifier exposes a **pluggable adapter interface**; Rocq is implemented
first; Lean, Agda, and Isabelle are stubs.

## Cost models

A complexity claim is meaningless without saying **what one step costs**. So
each work unit whose `claim_kind` is `complexity` or `closed-form` declares a
`cost_model = { kind, counts, notes }` (enforced by `work-units/schema.json`).
A cost model factors into three orthogonal axes — *language* × *counted
operations* × *proof technique* — of which the first two are recorded:

| `kind` | language | typical algorithms | technique |
|--------|----------|--------------------|-----------|
| **`func-ops`** (default) | small functional core | divide & conquer, recursion | instrumented count returned + structural induction |
| **`while-ops`** | WHILE imperative core | in-place loops (classic sorts, union-find, DP) | cost-annotated big-step semantics + loop invariants |
| `riscv` / `llvm` (optional) | concrete ISA / IR | machine-near claims | separate layer; not the default |

`counts` names the **dominant operation(s)** charged unit cost (e.g.
`["comparison"]`, `["key-comparison"]`, `["multiplication"]`), following the
analysis-of-algorithms convention of counting one dominant operation rather than
all elementary steps. We deliberately avoid pinning the project to a single
physical machine (e.g. MIX/MMIX): asymptotic claims should be machine-independent
and composable.

The two insertion-sort seeds show the design: the same `2·k ≤ n(n−1)` bound is
stated under `func-ops` (`insertion-sort-comparisons`) and `while-ops`
(`insertion-sort-comparisons-while`). The `while-ops` core is also the on-ramp
to **reversible** (R-WHILE / Janus-style) cost analysis — a planned
differentiating sub-corpus only this lab can supply.

## Reward model (why no crypto)

Contributors earn **non-transferable, non-redeemable reputation**: leaderboard
standing and credit in the corpus / papers. We deliberately avoid monetary or
token rewards:

- A self-issued, transferable token would likely be a *crypto-asset* under
  Japan's Payment Services Act, dragging in exchange-operator registration,
  AML/KYC, and criminal liability for operating unregistered — disproportionate
  for a research project. The regulatory ground is also mid-reform (PSA → FIEA
  migration expected ~2026–2027).
- Paying contributors in crypto pushes **miscellaneous-income tax** (up to ~55%)
  onto them. "Volunteer, then file taxes" does not recruit anyone.
- Folding@home itself reached ~millions of contributors on **non-redeemable
  credit + leaderboard + "this helps humanity"** — exactly the lever we have,
  with zero financial regulation.

Academic credit (co-authorship, named contributions) is the most valuable
currency here and is regulation-free. Because verification is mechanical, "only
kernel-passing contributions earn credit" can be enforced automatically.

## Legal / ethics notes

- **Theorems and algorithms are not copyrightable** (mathematical facts, ideas);
  their formalizations are fine to publish. Do **not** copy prose / exposition
  from textbooks into the corpus — reference and cite instead.
- The corpus is intended to double as a **curated benchmark** of
  "correctness + complexity" algorithm theorems — itself a contribution,
  analogous to how miniF2F / Lean Workbook became standard datasets.

## Open design questions (tracked, not yet decided)

- Work-unit granularity: whole theorem vs. lemma-level decomposition.
- Anti-spam / rate limiting on submissions without authentication.
- Sandbox model for running submitted proof scripts safely (see `verifier/`).
- Corpus storage: flat files in-repo vs. a database behind the coordinator.
- How the conjecture track hands candidates to the verify track (format).
