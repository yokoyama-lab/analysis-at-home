#!/usr/bin/env bash
# Verify the proof targets a PR adds or changes.
#
# For every added/modified file under work-units/<unit>/targets/<backend>/, look
# up that unit's `expected_theorem` (from unit.json) and run the kernel verifier
# verifier/verify.sh <backend> <file> <theorem>. Exits non-zero if any fails.
#
# Usage: tools/verify_changed.sh <base-ref> [only-backend]
#   <base-ref>     e.g. origin/main — the PR base to diff against
#   [only-backend] optional: restrict to rocq|lean|agda|isabelle (for per-job CI)
#
# Pure shell + grep (no python), so it runs inside the bare proof-assistant
# containers used in CI.
set -uo pipefail

base="${1:-origin/main}"
only="${2:-}"
root="$(cd "$(dirname "$0")/.." && pwd)"

mapfile -t files < <(git -C "$root" diff --name-only --diff-filter=AM "${base}...HEAD" 2>/dev/null)
if [ "${#files[@]}" -eq 0 ]; then
  # fall back to a plain two-dot diff if the merge-base form failed
  mapfile -t files < <(git -C "$root" diff --name-only --diff-filter=AM "${base}" 2>/dev/null)
fi

fail=0
checked=0
for f in "${files[@]}"; do
  case "$f" in
    work-units/*/targets/*/*) : ;;
    *) continue ;;
  esac
  rest="${f#work-units/}"
  unit="${rest%%/*}"
  bk="${rest#*/targets/}"; bk="${bk%%/*}"
  [ -z "$only" ] || [ "$bk" = "$only" ] || continue

  uj="$root/work-units/$unit/unit.json"
  [ -f "$uj" ] || { echo "SKIP  $f  (no unit.json)"; continue; }
  thm="$(grep -o '"expected_theorem"[[:space:]]*:[[:space:]]*"[^"]*"' "$uj" | head -1 | sed 's/.*: *"//; s/".*//')"
  [ -n "$thm" ] || { echo "SKIP  $f  (unit has no expected_theorem)"; continue; }

  echo "::group::verify ${f}  (${bk} : ${thm})"
  out="$(bash "$root/verifier/verify.sh" "$bk" "$root/$f" "$thm" 2>&1)"
  echo "$out"
  echo "::endgroup::"
  checked=$((checked + 1))
  if printf '%s' "$out" | grep -q '"accepted": true'; then
    echo "PASS  $f"
  else
    echo "FAIL  $f"
    fail=1
  fi
done

echo "checked ${checked} target file(s)"
exit "$fail"
