# verifier — the trust anchor

This is the only component that decides whether a submission is accepted. It
runs a submitted proof through a proof assistant's **trusted kernel** and
reports pass/fail. It does **not** call any LLM.

A submission is **accepted** iff the proof assistant both:

1. **compiles** the submitted source with no errors, and
2. proves the named theorem with **no axioms** — for Rocq, `Print Assumptions
   <theorem>` reports *"Closed under the global context"*.

Check (2) is what makes acceptance trustworthy: it catches `Admitted` / `admit`
/ `Axiom` robustly (they surface as axioms), and — unlike a textual grep for the
word "Admitted" — it does **not** false-positive on that word appearing in a
comment. Because acceptance is purely mechanical, the project never has to trust
the contributor or the LLM that produced the proof — see [`../docs/design.md`](../docs/design.md).

## Interface

`verify.sh <backend> <submission-file> <theorem-name>`

- `backend` ∈ `rocq` | `lean` | `agda` | `isabelle`
- `submission-file`: the candidate proof source submitted by a contributor
- `theorem-name`: the identifier the submission must prove with no axioms (a work
  unit declares it as `expected_theorem`)

Exit code `0` = accepted, non-zero = rejected. A machine-readable verdict is
printed to stdout as JSON: `{ "accepted": bool, "reason": string }`.

Adapters live in `adapters/<backend>.sh` and implement the actual kernel call:

| backend | kernel check | completeness check |
|---------|--------------|--------------------|
| `rocq` | `coqc` compiles | `Print Assumptions` ⇒ "Closed under the global context" |
| `lean` | `lean` compiles | `#print axioms` ⇒ no `sorryAx` (standard axioms OK) |
| `isabelle` | `isabelle build` (one-theory session) | no `sorry`/`oops` (textual, Phase 1) |
| `agda` | `agda --safe` type-checks | no `postulate` (textual, Phase 1) |

The `binary-counter-increments` theorem is verified in **rocq, lean, and
isabelle** (three independent kernels). `isabelle build` is heavy (loads the HOL
image) so the isabelle adapter is not wired into CI yet. The textual
sorry/oops/postulate checks for isabelle/agda are a Phase 1 simplification (see
the per-adapter notes) — a kernel-level check is the robust follow-up.

## Signature equivalence (TODO — Phase 1)

`expected_theorem` pins the *name* and (via `Print Assumptions`) the *axiom-free*
status, but a submission could still prove a **weaker statement** under that
name. The remaining check is to confirm the submission proves the **same
statement** as the unit's seed, e.g. by appending `Check (<thm> : <expected_type>).`
where `<expected_type>` comes from the seed.

## Sandbox (TODO — Phase 1)

Submitted proof scripts are untrusted code and must run in isolation
(container / no network / CPU+time limits / read-only FS except a scratch dir).
The current adapters run `coqc` directly with **no sandbox** — fine for local
trusted use, **not** safe for accepting submissions from the internet. Wiring a
real sandbox is a Phase 1 blocker before the public web MVP goes live.
