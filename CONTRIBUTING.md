# Contributing to analysis@home

You contribute by turning an **open work unit** into a **kernel-checked proof**.
You bring your own LLM; we re-verify what you submit. Nothing you submit is
trusted — the kernel decides.

## Quick path (manual, today)

1. Pick an open unit under [`work-units/`](work-units/) (start with
   `insertion-sort-comparisons`).
2. Open its `prompt-template.md`, copy the prompt into **your own** LLM
   (Claude, etc.).
3. Take the proof it returns. Verify it locally:

   ```bash
   # Rocq example:
   verifier/verify.sh rocq /path/to/your_proof.v \
     work-units/insertion-sort-comparisons/targets/rocq/InsertionSortComparisons.v
   ```

   A `{"accepted": true, ...}` verdict means the kernel accepted a complete
   proof (no `Admitted`/`Axiom`).
4. Open a PR that replaces the unit's `targets/<backend>/...` seed with your
   proved version and flips the matching `status` entry to `verified`.

> The web MVP (`web/`) will automate steps 2–4. Until it's wired (Phase 1), the
> manual path above is the way.

## Rules

- **Never paste credentials or API keys anywhere** in this project. Submissions
  are proof source only.
- A submission must prove the **same statement** as the seed — don't weaken the
  theorem or change the fixed cost-model definitions (`insert`/`isort`/…). This
  is enforced for changed targets by a **signature-lock**
  (`tools/signature_lock.sh`): if the target already exists on the base branch,
  CI requires the statement of the named theorem to be identical (only the proof
  may change). A brand-new backend port has no prior statement to lock against,
  so it is kernel-checked and flagged for human review.
- No `Admitted`, `admit`, `Axiom`, `Parameter`, `sorry`, or
  `--allow-unsolved-metas`. Smuggled axioms are rejected. CI kernel-checks every
  changed proof target across **all four backends** (rocq/lean/agda/isabelle);
  the lean/agda/isabelle toolchains install only when the PR touches that backend.
- It's fine if a claim turns out **not** provable in some backend — say so in
  the PR. "Couldn't be done in backend X" is useful signal, not a failure.

## Adding a new work unit

See [`docs/work-unit-format.md`](docs/work-unit-format.md). A unit needs
`unit.json` (validated against `work-units/schema.json`), a human `statement.md`,
a `prompt-template.md`, and at least one `targets/<backend>/` seed whose theorem
is `Admitted.`. This is how you contribute a **cost** claim too — `claim_kind`
may be `worst-case` / `best-case` / `expected-cost` / `complexity` /
`closed-form` (not only `correctness`); the kernel checks the cost theorem the
same way.

## Contributing to the conjecture track (cost distributions & limit laws)

The conjecture track *computes* a cost distribution, its exact mean, and its
limiting law — fast, but **not trusted**. Two ways to contribute:

1. **Promote a computed mean to a theorem (a "kernel twin").** The board lists
   distributions that have an exact computed mean but no verified twin yet. Prove
   that mean as a normal work unit and link the evidence from `unit.json`:
   `"conjecture_artifact": "tools/conjecture/results/<name>.json"`. The board then
   shows the conjecture and its kernel-checked twin side by side.
2. **Add a new distribution / limit law.** Add a model to
   [`tools/conjecture/conjecture.py`](tools/conjecture/conjecture.py) (pure
   stdlib — exact `Fraction` arithmetic, exhaustive enumeration, KS-fit to the
   candidate limit laws) and commit the regenerated `results/*.json`. CI re-runs
   the solver and **rejects any result that does not reproduce** from the
   committed script (`tools/check_conjecture_reproducible.sh`) — so a computed
   contribution is at least deterministically reproducible by anyone.

## Credit

Verified contributions are credited in the corpus and on the leaderboard — a
non-monetary, non-transferable reputation. See [`docs/design.md`](docs/design.md)
for why we deliberately avoid token/monetary rewards.

## License of contributions

By contributing you agree your code is licensed Apache-2.0 and your
formalizations/work-units under CC-BY-4.0 (see [`README.md`](README.md)).
