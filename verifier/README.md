# verifier — the trust anchor

This is the only component that decides whether a submission is accepted. It
runs a submitted proof through a proof assistant's **trusted kernel** and
reports pass/fail. It does **not** call any LLM.

A submission is **accepted** iff:

1. the proof assistant compiles the submitted source with **no errors**, and
2. the source contains **no `Admitted` / `admit` / `Axiom` / `sorry`** and adds
   no axioms (an incomplete or axiom-smuggled proof is a rejection).

Because acceptance is purely mechanical, the project never has to trust the
contributor or the LLM that produced the proof — see [`../docs/design.md`](../docs/design.md).

## Interface

`verify.sh <backend> <submission-file> <expected-signature-file>`

- `backend` ∈ `rocq` | `lean` | `agda` | `isabelle`
- `submission-file`: the candidate proof source submitted by a contributor
- `expected-signature-file`: the seed file for the unit; the submission must
  prove the **same** statement (the seed's definitions + theorem signature),
  not a weaker one it made up. (Signature-equivalence check: TODO — Phase 1.)

Exit code `0` = accepted, non-zero = rejected. A machine-readable verdict is
printed to stdout as JSON: `{ "accepted": bool, "reason": string }`.

Adapters live in `adapters/<backend>.sh` and implement the actual kernel call.
Only `rocq` is wired up; `lean`, `agda`, and `isabelle` are stubs.

## Sandbox (TODO — Phase 1)

Submitted proof scripts are untrusted code and must run in isolation
(container / no network / CPU+time limits / read-only FS except a scratch dir).
The current adapters run `coqc` directly with **no sandbox** — fine for local
trusted use, **not** safe for accepting submissions from the internet. Wiring a
real sandbox is a Phase 1 blocker before the public web MVP goes live.
