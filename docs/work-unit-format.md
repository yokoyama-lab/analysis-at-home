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

## Translation is itself a work unit

If a unit lists a backend with no file under `targets/<backend>/`, producing
that rendition (informal → formal statement, still `Admitted.`) is a
dispatchable task. This keeps human load near zero and lets us fan out across
kernels.
