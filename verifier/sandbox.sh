#!/usr/bin/env bash
# Run "$@" in a sandbox: no network, the filesystem read-only except the
# scratch dir $AAH_SANDBOX_RW, with CPU/memory/file-size rlimits and a wall-clock
# timeout. Submitted proof scripts are untrusted code, so the kernel that checks
# them must run confined.
#
# Tunables (env): AAH_SANDBOX_RW (scratch+cwd, default $PWD),
#   AAH_SANDBOX_CPU (s, default 90), AAH_SANDBOX_WALL (s, default 120),
#   AAH_SANDBOX_FSIZE (KB max file, default 200000).
# NOTE: we do NOT cap address space (ulimit -v): OCaml 5 (Rocq) and Lean reserve
#   huge *virtual* memory regardless of real use, so -v makes them abort.
#   Memory must be bounded with cgroups on a real deployment; here the CPU-time
#   and wall-clock limits bound runaway work.
# If bwrap is unavailable it falls back to rlimits+timeout only (no FS/net
# isolation) and warns on stderr.
set -euo pipefail

rw="${AAH_SANDBOX_RW:-$PWD}"
cpu="${AAH_SANDBOX_CPU:-90}"
wall="${AAH_SANDBOX_WALL:-120}"
fsize="${AAH_SANDBOX_FSIZE:-200000}"

inner="ulimit -t ${cpu} -f ${fsize} 2>/dev/null || true; exec \"\$@\""

if command -v bwrap >/dev/null 2>&1; then
  exec timeout --signal=KILL "${wall}" bwrap \
    --ro-bind / / \
    --dev /dev --proc /proc \
    --bind "$rw" "$rw" \
    --unshare-net --unshare-pid --unshare-ipc --unshare-uts \
    --die-with-parent --new-session \
    --chdir "$rw" \
    -- bash -c "$inner" _ "$@"
else
  echo "verifier/sandbox.sh: bwrap not found — running with rlimits+timeout only (no FS/net isolation)" >&2
  cd "$rw"
  exec timeout --signal=KILL "${wall}" bash -c "$inner" _ "$@"
fi
