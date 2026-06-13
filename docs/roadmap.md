# Roadmap

Phases are sequential; each ends with a concrete, checkable milestone.

## Phase 0 — Scaffold ✅ (this commit)

Make the empty repo "design-visible": interfaces and types fixed before logic.

- [x] `docs/` — design, work-unit format, roadmap
- [x] `work-units/` — JSON schema + first seed unit (insertion-sort comparisons),
      with an informal statement, a prompt template, and a minimal Rocq `.v`
      whose theorem is `Admitted.`
- [x] `verifier/` — pluggable adapter interface + minimal Rocq adapter glue
      (sandbox stubbed)
- [x] `coordinator/` — in-memory stub: dispatch → submit → verify → record
- [x] `web/` — static MVP: show a ready-made prompt, paste the proof back
- [x] CI that type-checks **only** the seed Rocq statement (no LLM, no secrets)

**Milestone:** repo communicates the architecture; `coqc` accepts the seed `.v`.

## Phase 1 — Push one theorem end-to-end (~2 weeks)

One vertical slice that actually works, for **insertion sort comparison count**.

- [ ] Replace the `Admitted.` worst-case bound with a real Rocq proof
      (`2 * comparisons l <= length l * (length l - 1)`).
- [ ] Add the functional-correctness unit (sorted permutation) alongside cost.
- [ ] Coordinator: real submission intake → invoke verifier → persist `verified`.
- [ ] Web MVP: a third party pastes the prompt into their own LLM, submits the
      result, and sees it auto-marked `verified`.

**Milestone:** an outside contributor verifies a theorem without us trusting them.

## Phase 2 — The two-track pipeline (research core)

- [ ] Conjecture track: SymPy / computer-algebra harness that emits candidate
      closed forms + measured runtime distributions for a target algorithm.
- [ ] Verify track: lift a candidate into a Rocq cost theorem (time-credit style).
- [ ] Demonstrate on a previously "stuck" result to show the pipeline's value.

**Milestone:** a conjecture-track candidate is promoted to a kernel-checked theorem.

## Phase 3 — Resident agent + corpus growth

- [ ] `pip install`-able local agent: fetch unit → run the contributor's own LLM
      → submit. (Credentials stay local.)
- [ ] Multi-backend: Lean, Agda, and Isabelle adapters; "translate to backend X" work units.
- [ ] Leaderboard + CONTRIBUTORS, driven purely by kernel-passing submissions.
- [ ] Publish the corpus as a citable "correctness + complexity" benchmark.

**Milestone:** the corpus grows from external contributions on autopilot.
