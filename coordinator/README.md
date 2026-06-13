# coordinator — work dispatch & verified-status ledger

Coordinates work units and records which have been kernel-verified. It is a
**dumb, trustless** broker:

- serves the [`web/`](../web/) MVP and lists open work units (`/api/units`),
- hands out the ready-to-paste prompt for a unit (`/api/prompt`),
- accepts a candidate proof (`/api/submit`) — *source text only, never
  credentials*,
- invokes the [`verifier`](../verifier/) to re-check it with the kernel,
- records `verified` only when the kernel accepts.

It **never** calls an LLM. See [`../docs/design.md`](../docs/design.md).

## Run the vertical slice

Requires Node ≥ 22.6 (runs TypeScript natively) and a Rocq toolchain on `PATH`
(`coqc` or `rocq`) for the verifier.

```bash
npm install            # once, for @types/node + typescript
npm start              # node src/server.ts  -> http://localhost:8787
```

Then open the page, pick an open unit, paste its prompt into your own LLM, paste
the proof back, and submit — the server re-checks it with the kernel and flips
the status to `verified` on success.

### HTTP API

- `GET /api/units` → open `{unitId, backend, title, status}` targets
- `GET /api/prompt?unit=<id>` → `{prompt, expected_theorem}`
- `POST /api/submit` `{unitId, backend, source}` → `{accepted, reason, status}`

## Files

- `src/types.ts` — shared types (mirrors `work-units/schema.json`)
- `src/coordinator.ts` — the in-memory state-machine reference model (`open →
  submitted → verified`), used by `npm run typecheck`
- `src/server.ts` — the runnable HTTP server (loads units from disk, shells out
  to `verifier/verify.sh`); status is in-memory and resets to the on-disk
  `unit.json` on restart

## Not yet (Phase 1)

Persistence, rate-limiting/anti-spam without auth, and running the verifier
inside a sandbox (see `verifier/README.md`) — all required before exposing this
publicly.

## Dev

```bash
npm run typecheck
```
