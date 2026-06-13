# coordinator — work dispatch & verified-status ledger

Coordinates work units and records which have been kernel-verified. It is a
**dumb, trustless** broker:

- hands out open work units (`dispatch`),
- accepts a candidate proof (`submit`) — *source text only, never credentials*,
- invokes the [`verifier`](../verifier/) to re-check it,
- records `verified` only when the kernel accepts.

It **never** calls an LLM. See [`../docs/design.md`](../docs/design.md).

## Status: stub

`src/coordinator.ts` is an in-memory reference implementation with clear `TODO`s.
It defines the API surface and the state machine; it does not persist, serve
HTTP, rate-limit, or sandbox. Those are Phase 1 work.

```
dispatch(backend?)          -> next open WorkUnitRef
submit({unitId, backend, source}) -> Verdict   (calls verifier, updates status)
status(unitId)              -> per-backend status
```

## Dev

```bash
npm install
npm run typecheck
```
