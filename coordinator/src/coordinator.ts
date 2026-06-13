// In-memory reference coordinator for analysis@home.
//
// STUB: defines the API surface and the open -> submitted -> verified state
// machine. No persistence, no HTTP server, no rate limiting, no sandbox — all
// Phase 1 work (see TODOs). It NEVER calls an LLM and NEVER receives
// credentials; submissions carry proof source only.

import type {
  Backend,
  Submission,
  Verdict,
  WorkUnit,
  WorkUnitRef,
} from "./types.js";

export class Coordinator {
  private readonly units = new Map<string, WorkUnit>();

  /** Register a work unit (Phase 1: load these from work-units/ on disk). */
  register(unit: WorkUnit): void {
    this.units.set(unit.id, unit);
  }

  /** Hand out the next open unit, optionally constrained to one backend. */
  dispatch(backend?: Backend): WorkUnitRef | null {
    for (const unit of this.units.values()) {
      for (const b of unit.targets) {
        if (backend && b !== backend) continue;
        if (unit.status[b] === "open") {
          return {
            unitId: unit.id,
            backend: b,
            title: unit.title,
            // TODO: resolve to a real served path / fetch the prompt contents.
            promptPath: `work-units/${unit.id}/${unit.prompt_template}`,
          };
        }
      }
    }
    return null;
  }

  /**
   * Accept a candidate, re-check it with the kernel, update status.
   * The verdict comes ONLY from the verifier — never the contributor.
   */
  async submit(
    s: Submission,
    verify: (s: Submission) => Promise<Verdict>,
  ): Promise<Verdict> {
    const unit = this.units.get(s.unitId);
    if (!unit) return { accepted: false, reason: `unknown unit: ${s.unitId}` };
    if (!unit.targets.includes(s.backend)) {
      return { accepted: false, reason: `backend ${s.backend} not in scope` };
    }

    unit.status[s.backend] = "submitted";

    // TODO (Phase 1): shell out to verifier/verify.sh inside a sandbox,
    // and enforce signature-equivalence against the seed file.
    const verdict = await verify(s);

    // Trustless: verified iff the kernel accepted; otherwise back to open.
    unit.status[s.backend] = verdict.accepted ? "verified" : "open";
    return verdict;
  }

  status(unitId: string): Partial<Record<Backend, string>> | null {
    return this.units.get(unitId)?.status ?? null;
  }
}
