# Work-unit format

A **work unit** is one open problem the project wants proven. It is
backend-agnostic: it states a claim informally and tracks, per backend, whether
a kernel-checked proof exists yet.

Each work unit is a directory under `work-units/<id>/`:

```
work-units/<id>/
  unit.json          # metadata, validated against work-units/schema.json
  statement.md       # the informal claim + context + references (human-readable)
  prompt-template.md # the ready-to-paste prompt a contributor gives their LLM
  targets/
    rocq/*.v         # per-backend statement; theorem starts as `Admitted.`
    lean/*.lean      # (optional, may not exist yet)
    agda/*.agda      # (optional, may not exist yet)
    isabelle/*.thy   # (optional, may not exist yet)
```

## `unit.json` fields

| field | type | meaning |
|-------|------|---------|
| `id` | string | stable kebab-case identifier, matches the directory name |
| `title` | string | one-line human title |
| `statement_informal` | string | the claim in prose (kept short; full text in `statement.md`) |
| `domain` | string | e.g. `sorting`, `string-matching`, `graph` |
| `claim_kind` | enum | `correctness` \| `complexity` \| `closed-form` |
| `targets` | string[] | backends in scope, subset of `rocq` \| `lean` \| `agda` \| `isabelle` |
| `prompt_template` | string | path to the prompt file, relative to the unit dir |
| `references` | string[] | citations (NOT copied prose — pointers only) |
| `status` | object | per-backend status: `open` \| `submitted` \| `verified` |

`status` is keyed by backend, e.g. `{ "rocq": "open", "lean": "open" }`. A unit
is "done" when at least one backend reaches `verified`; reaching it in more is
bonus signal.

## Lifecycle

```
open ──(a contributor submits a candidate proof)──▶ submitted
submitted ──(kernel accepts)──▶ verified
submitted ──(kernel rejects)──▶ open      # nothing trusted, just try again
```

The transition to `verified` is performed **only** by the verifier after the
kernel accepts — never by a contributor's say-so. See `docs/design.md`.

## Decomposition: small leaves that assemble into a theorem

To make work **reliably completable**, a hard theorem is sliced into small,
independently-checkable pieces so many contributors each finish one. A unit
declares its `kind`:

- **`theorem`** (default) — a whole self-contained theorem.
- **`leaf`** — ONE lemma. The unit of crowd work: small (often a single
  `induction`/`inversion` + `lia`), `difficulty`-tagged (★1–5), and depending
  only on other leaves' **statements** (`depends_on`), never their proofs — so
  leaves are done in any order, in parallel.
- **`assembly`** — the glue: proves the main theorem from the leaf lemmas, with
  no new heavy reasoning.

A leaf's prompt is self-contained = shared spec + its `depends_on` lemma
statements (as `Admitted`) + the lemma to prove. The kernel checks each leaf;
the theorem is **certified** only when every leaf is discharged and the
assembled `Print Assumptions <main>` reports *"Closed under the global
context"* — i.e. nothing is assumed.

A worked, runnable example (the `while-ops` theorem split into 10 leaves + an
assembly + `assemble.sh`, with a `leaves.json` manifest) lives in
[`../work-units/insertion-sort-comparisons-while/decomposition/`](../work-units/insertion-sort-comparisons-while/decomposition/).

**Adaptive grain:** if a leaf can't be one-shot after several attempts, it is
"too big" and should be split further (its internal `assert`s are the natural
sub-leaves). Failures drive finer decomposition until every leaf is reliable.

## Translation is itself a work unit

If a unit lists a backend with no file under `targets/<backend>/`, producing
that rendition (informal → formal statement, still `Admitted.`) is a
dispatchable task. This keeps human load near zero and lets us fan out across
kernels.
