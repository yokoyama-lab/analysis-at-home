#!/usr/bin/env bash
# Isabelle/HOL adapter.
#
# Accept iff `isabelle build` checks a one-theory session containing the
# submission AND the submission uses no `sorry`/`oops` (Isabelle's incompleteness
# markers). The <theorem-name> must appear in the theory.
#
# Limitations (Phase 1): (a) the sorry/oops check is textual (comments would
# false-positive — keep them out); (b) `isabelle build` is heavy (loads the HOL
# image), so this adapter is not wired into CI yet — it is meant for local /
# dedicated-runner verification.
#
# Args: <submission.thy> <theorem-name>
set -euo pipefail
submission="${1:-}"
theorem="${2:-}"
verdict() { printf '{"accepted": %s, "reason": "%s"}\n' "$1" "$2"; }
clean() { printf '%s' "$1" | tr '\n' ' ' | sed 's/"/\\"/g' | cut -c1-240; }

command -v isabelle >/dev/null 2>&1 || { verdict false "isabelle not installed"; exit 2; }
[ -n "$theorem" ] || { verdict false "no theorem name given"; exit 2; }

if grep -Eqw 'sorry|oops' "$submission"; then
  verdict false "submission uses sorry/oops"; exit 1
fi
grep -q "$theorem" "$submission" || { verdict false "theorem ${theorem} not found"; exit 1; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cp "$submission" "$work/Submission.thy"
cat > "$work/ROOT" <<ROOT
session AAH = HOL +
  theories
    Submission
ROOT
if ( cd "$work" && isabelle build -D . ) >"$work/out" 2>&1; then
  verdict true "isabelle build checked ${theorem}; no sorry/oops"
else
  verdict false "isabelle rejected: $(clean "$(tail -c 400 "$work/out")")"
  exit 1
fi
