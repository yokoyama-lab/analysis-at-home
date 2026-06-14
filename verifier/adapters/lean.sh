#!/usr/bin/env bash
# Lean 4 adapter.
#
# Accept iff `lean` compiles the submission AND the named theorem does NOT
# depend on `sorryAx` (Lean's marker for `sorry`/`admit`). The standard
# foundational axioms (propext, Classical.choice, Quot.sound) are part of Lean's
# logic and are allowed — only sorry is a cheat.
#
# Args: <submission.lean> <theorem-name>
set -euo pipefail
submission="${1:-}"
theorem="${2:-}"
verdict() { printf '{"accepted": %s, "reason": "%s"}\n' "$1" "$2"; }
clean() { printf '%s' "$1" | tr '\n' ' ' | sed 's/"/\\"/g' | cut -c1-240; }

command -v lean >/dev/null 2>&1 || { verdict false "lean not installed"; exit 2; }
[ -n "$theorem" ] || { verdict false "no theorem name given"; exit 2; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cp "$submission" "$work/Sub.lean"
printf '\n#print axioms %s\n' "$theorem" >> "$work/Sub.lean"

if ( cd "$work" && lean Sub.lean ) >"$work/out" 2>&1; then
  if grep -q "sorryAx" "$work/out"; then
    verdict false "depends on sorryAx (sorry/admit): $(clean "$(cat "$work/out")")"
    exit 1
  fi
  verdict true "lean-checked: ${theorem} does not depend on sorryAx"
else
  verdict false "lean rejected: $(clean "$(cat "$work/out")")"
  exit 1
fi
