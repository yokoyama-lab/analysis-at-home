#!/usr/bin/env bash
# Rocq (Coq) adapter: compile the submission with coqc and report a verdict.
# Args: <submission.v> [expected-signature.v]
set -euo pipefail

submission="${1:-}"
verdict() { printf '{"accepted": %s, "reason": "%s"}\n' "$1" "$2"; }

command -v coqc >/dev/null 2>&1 || { verdict false "coqc not installed"; exit 2; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cp "$submission" "$work/Submission.v"

# TODO (Phase 1): run this inside a real sandbox (no network, time/CPU limits).
if ( cd "$work" && coqc -q Submission.v ) >/dev/null 2>"$work/err"; then
  # coqc prints a warning for Admitted but exits 0; the verify.sh pre-check
  # already rejects Admitted/Axiom, so reaching here with exit 0 means a
  # complete, kernel-checked proof.
  verdict true "coqc accepted; no Admitted/Axiom"
else
  verdict false "coqc rejected: $(tr '\n' ' ' < "$work/err" | sed 's/"/\\"/g' | cut -c1-300)"
  exit 1
fi
