# analysis@home

**Spare AI, turned into proven math.**

Point your LLM at an open problem. Get back a proof the kernel actually checked.
No trust required.

> Folding@home for proofs.

---

## What this is

analysis@home turns spare LLM capacity into **machine-checked mathematics about
algorithms** — not just _"it works"_, but _"it runs in O(n log n)"_, proven by a
proof-assistant kernel.

Contributors run their **own** LLM (Claude, or anything else) against open *work
units* — an unproven complexity bound, a conjectured closed form, an algorithm
still waiting for its correctness proof — and submit candidate proofs. The
project re-checks every submission with a proof-assistant kernel
(**Rocq / Lean / Agda / Isabelle**) and keeps only what holds.

Because every contribution is **verified rather than trusted**, a corpus of
certified correctness and cost bounds grows from many hands — without anyone
having to trust the hands.

## How it works

**1 — Grab a work unit.**
An unproven complexity bound. A conjectured closed form. An algorithm still
waiting for its correctness proof.

**2 — Run your own LLM on it.**
Your machine, your account, your spare capacity. **Credentials never leave your
laptop.** The translation of an informal statement into a specific kernel
(Rocq / Lean / Agda / Isabelle) is itself a work unit an LLM can do — so the human load is
near zero.

**3 — Submit.**
The kernel re-checks every line. If it holds, it lands in the corpus —
permanently, and provably.

## Why it's different

- 🔒 **Verified, not trusted.** We don't care who — or what — wrote the proof.
  The kernel does the believing, so anyone can contribute and nobody has to be
  trusted. The server **never** calls an LLM and **never** stores your
  credentials.
- 📈 **Correctness _and_ cost.** Machine-checked complexity, not just
  functional correctness — the part competition-math-focused LLM-proof projects
  skip.
- 🌐 **Bring your own LLM.** We coordinate the work and re-verify the results.
  Your unused capacity stops going to waste.

## The two-track pipeline

| Track | Tooling | Output |
|-------|---------|--------|
| **Conjecture** | Python / SymPy, computer algebra, runtime-distribution experiments | _candidate_ closed forms & bounds (fast, **unproven**) |
| **Verify** | Rocq / Lean / Agda / Isabelle kernel (cost via time-credit style reasoning) | **theorems** |

A claim is only called *proven* once it has passed the verify track. The
conjecture track is a hypothesis generator, never the final word.

## Status

🚧 **Phase 0 — scaffold.** Interfaces and the first seed work unit are in place;
business logic is stubbed (see `TODO`s). The first end-to-end target is the
worst-case **comparison count of insertion sort** (`work-units/insertion-sort-comparisons`).

See [`docs/roadmap.md`](docs/roadmap.md) for the plan.

## Layout

```
docs/         design notes, work-unit format, roadmap
work-units/   the open problems + per-backend statements (seed: insertion sort)
verifier/     pluggable kernel adapters (Rocq / Lean / Agda / Isabelle) — the trust anchor
coordinator/  dispatch work units, accept submissions, record verified status
web/          minimal "paste prompt → paste proof back" MVP, no auth
```

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md). Verified contributors are credited in
the corpus and on the leaderboard — a non-monetary, non-transferable
reputation (deliberately: see [`docs/design.md`](docs/design.md) on why we avoid
token rewards).

## License

- **Code:** Apache-2.0 (see [`LICENSE`](LICENSE)).
- **Proof corpus / work units:** CC-BY-4.0 (planned; see `docs/design.md`).
