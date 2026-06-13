#!/usr/bin/env bash
# analysis@home verifier — pluggable kernel dispatch.
#
# Usage: verify.sh <backend> <submission-file> [expected-signature-file]
# Exit 0 = accepted, non-zero = rejected.
# Prints a JSON verdict to stdout: {"accepted": bool, "reason": "..."}.
#
# NOTE: runs the kernel directly with NO sandbox yet (see README "Sandbox").
set -euo pipefail

backend="${1:-}"
submission="${2:-}"
expected="${3:-}"

verdict() { printf '{"accepted": %s, "reason": "%s"}\n' "$1" "$2"; }
reject()  { verdict false "$1"; exit 1; }

[ -n "$backend" ]    || reject "no backend given"
[ -f "$submission" ] || reject "submission file not found: ${submission}"

adapter="$(dirname "$0")/adapters/${backend}.sh"
[ -f "$adapter" ] || reject "no adapter for backend: ${backend}"

# Reject obvious incompleteness/axiom-smuggling before even invoking the kernel.
# (Per-backend adapters MUST also enforce this; this is a fast pre-check.)
if grep -Eqn '\b(Admitted|admit|Axiom|Parameter|sorry|oops|postulate)\b' "$submission"; then
  reject "submission contains Admitted/admit/Axiom/sorry/oops/postulate"
fi

# TODO (Phase 1): verify the submission proves the SAME statement as
# "$expected" (signature-equivalence), not a weaker self-chosen one.

# Delegate to the backend adapter; it owns the kernel invocation + verdict.
exec bash "$adapter" "$submission" "$expected"
