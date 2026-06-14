#!/usr/bin/env bash
# Run "$@" in a sandbox: no network, the filesystem read-only except the scratch
# dir $AAH_SANDBOX_RW, with CPU/file-size rlimits, a wall-clock timeout, and a
# cgroup memory cap. Submitted proof scripts are untrusted code, so the kernel
# that checks them must run confined.
#
# Tunables (env): AAH_SANDBOX_RW (scratch+cwd, default $PWD),
#   AAH_SANDBOX_CPU (s, default 90), AAH_SANDBOX_WALL (s, default 120),
#   AAH_SANDBOX_FSIZE (KB max file, default 200000),
#   AAH_SANDBOX_MEM (cgroup MemoryMax, default 4G).
# Memory is capped via a systemd user scope (cgroup RSS limit) when available —
# NOT ulimit -v, which OCaml 5 (Rocq) and Lean abort under (they reserve huge
# *virtual* space). Where bwrap is absent it falls back to rlimits+timeout only
# (no FS/net isolation) and warns; where systemd-run is absent the memory cap is
# skipped (the CPU+wall limits still bound runaway work).
set -euo pipefail

rw="${AAH_SANDBOX_RW:-$PWD}"
cpu="${AAH_SANDBOX_CPU:-90}"
wall="${AAH_SANDBOX_WALL:-120}"
fsize="${AAH_SANDBOX_FSIZE:-200000}"
mem="${AAH_SANDBOX_MEM:-4G}"

inner="cd \"$rw\"; ulimit -t ${cpu} -f ${fsize} 2>/dev/null || true; exec \"\$@\""

if command -v bwrap >/dev/null 2>&1; then
  cmd=(bwrap --ro-bind / / --dev /dev --proc /proc --bind "$rw" "$rw"
       --unshare-net --unshare-pid --unshare-ipc --unshare-uts
       --die-with-parent --new-session --chdir "$rw"
       -- bash -c "$inner" _ "$@")
else
  echo "verifier/sandbox.sh: bwrap not found — rlimits+timeout only (no FS/net isolation)" >&2
  cmd=(bash -c "$inner" _ "$@")
fi

# Wall-clock timeout around the kernel.
cmd=(timeout --signal=KILL "$wall" "${cmd[@]}")

# Bound memory with a cgroup (systemd user scope) when available.
if command -v systemd-run >/dev/null 2>&1 \
   && systemd-run --user --scope -q -p MemoryMax="$mem" true >/dev/null 2>&1; then
  exec systemd-run --user --scope -q -p MemoryMax="$mem" -p MemorySwapMax=0 -- "${cmd[@]}"
else
  exec "${cmd[@]}"
fi
