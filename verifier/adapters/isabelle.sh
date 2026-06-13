#!/usr/bin/env bash
# Isabelle/HOL adapter — STUB (Phase 3).
# Should check the submitted theory with `isabelle build` (or `isabelle process`)
# and reject it if it uses `sorry`, `oops`, or unproved `axiomatization`/
# `consts` smuggling. Acceptance = the theory builds with no `sorry`.
set -euo pipefail
printf '{"accepted": false, "reason": "isabelle adapter not implemented (stub)"}\n'
exit 3
