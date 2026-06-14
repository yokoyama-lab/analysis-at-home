#!/usr/bin/env bash
# Agda adapter.
#
# Accept iff `agda --safe` type-checks the submission (which rejects unsafe
# features and any unsolved holes `?`/`{!!}`), AND the file declares no
# `postulate` (Agda's axiom escape hatch). The <theorem-name> identifier must
# appear as a top-level definition.
#
# Limitation (Phase 1): the postulate check is textual; a more robust check
# would inspect the type-checked module. Comments mentioning "postulate" would
# false-positive — keep them out of submissions.
#
# Args: <submission.agda> <theorem-name>
set -euo pipefail
submission="${1:-}"
theorem="${2:-}"
verdict() { printf '{"accepted": %s, "reason": "%s"}\n' "$1" "$2"; }
clean() { printf '%s' "$1" | tr '\n' ' ' | sed 's/"/\\"/g' | cut -c1-240; }

command -v agda >/dev/null 2>&1 || { verdict false "agda not installed"; exit 2; }
[ -n "$theorem" ] || { verdict false "no theorem name given"; exit 2; }

if grep -Eq '^[[:space:]]*postulate\b' "$submission"; then
  verdict false "submission declares a postulate (axiom)"; exit 1
fi
grep -Eq "(^|[[:space:]])${theorem}([[:space:]]|:)" "$submission" \
  || { verdict false "theorem ${theorem} not found as a definition"; exit 1; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cp "$submission" "$work/Sub.agda"
if ( cd "$work" && agda --safe Sub.agda ) >"$work/out" 2>&1; then
  verdict true "agda --safe type-checked ${theorem}; no postulate"
else
  verdict false "agda rejected: $(clean "$(cat "$work/out")")"
  exit 1
fi
