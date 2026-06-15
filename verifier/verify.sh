#!/usr/bin/env bash
# analysis@home verifier — pluggable kernel dispatch.
#
# Usage: verify.sh <backend> <submission-file> <theorem-name>
# Exit 0 = accepted, non-zero = rejected.
# Prints a JSON verdict to stdout: {"accepted": bool, "reason": "..."}.
#
# The decision is made ONLY by a proof-assistant kernel (see the per-backend
# adapter), never by an LLM. <theorem-name> is the identifier the submission
# must prove with no axioms.
#
# NOTE: the adapters run the kernel directly with NO sandbox yet (see README
# "Sandbox") — fine for local/trusted use, not for public submissions.
set -euo pipefail

backend="${1:-}"
submission="${2:-}"
theorem="${3:-}"

verdict() { printf '{"accepted": %s, "reason": "%s"}\n' "$1" "$2"; }
reject()  { verdict false "$1"; exit 1; }

[ -n "$backend" ]    || reject "no backend given"
[ -f "$submission" ] || reject "submission file not found: ${submission}"
[ -n "$theorem" ]    || reject "no theorem name given"

adapter="$(dirname "$0")/adapters/${backend}.sh"
[ -f "$adapter" ] || reject "no adapter for backend: ${backend}"

# Signature-equivalence (that the submission proves the SAME statement, not just
# a same-named weaker one) is enforced one level up, in tools/verify_changed.sh
# via tools/signature_lock.sh: when a target already exists on the base branch,
# the submitted statement of <theorem-name> must match it (only the proof may
# change). New targets are kernel-checked here and flagged for human review.

# Delegate to the backend adapter; it owns the kernel invocation + verdict.
exec bash "$adapter" "$submission" "$theorem"
