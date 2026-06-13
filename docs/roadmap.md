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

## Phase 1 — Push one theorem end-to-end (in progress)

One vertical slice that actually works, for **insertion sort comparison count**.

- [x] Replace the `Admitted.` worst-case bound with a real Rocq proof
      (`2 * comparisons l <= length l * (length l - 1)`) — both the `func-ops`
      and `while-ops` units, kernel-checked, axiom-free.
- [x] Verifier: real trustless check — compile + `Print Assumptions` reports
      "Closed under the global context" (no naive grep false-positives).
- [x] Coordinator: real HTTP server, submission intake → invoke verifier →
      record `verified` (in-memory).
- [x] Web MVP: pick an open unit, paste the prompt into your own LLM, submit,
      and see it auto-marked `verified`.
- [ ] Signature-equivalence check (submission proves the *same* statement as the
      seed, not a weaker one) — see `verifier/README.md`.
- [ ] Sandbox the verifier before any public exposure.
- [ ] Persist verified status (currently in-memory; resets on restart).
- [ ] Add the functional-correctness unit (sorted permutation) alongside cost.

**Milestone:** an outside contributor verifies a theorem without us trusting
them — reached locally; remaining items harden it for public use.

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
