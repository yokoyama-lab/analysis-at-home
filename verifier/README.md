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

## Sandbox

Submitted proof scripts are untrusted code, so the kernel runs inside
[`sandbox.sh`](sandbox.sh) (bubblewrap): **no network**, the filesystem
**read-only except the scratch dir**, a new PID/IPC/UTS namespace, plus a
CPU-time and wall-clock limit. The `rocq`, `lean`, and `agda` adapters invoke
the kernel through it.

Memory is capped via a **cgroup** (a `systemd --user` scope with `MemoryMax`),
not `ulimit -v` — OCaml 5 (Rocq) and Lean reserve huge *virtual* space and abort
under `-v`, but a cgroup limits real RSS (verified: a 20M cap OOM-kills `coqc`).
Where `systemd-run` is absent the cap is skipped (CPU+wall limits still apply);
where `bwrap` is absent, `sandbox.sh` falls back to rlimits+timeout only and
warns. The `isabelle` adapter is **not** sandboxed yet (it needs a writable
Isabelle home) and is intended for a dedicated runner.
