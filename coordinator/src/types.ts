// Shared types for analysis@home. Mirrors work-units/schema.json.

export type Backend = "rocq" | "lean" | "agda" | "isabelle";

export type UnitStatus = "open" | "submitted" | "verified";

export type ClaimKind = "correctness" | "complexity" | "closed-form";

/** A work unit as stored in work-units/<id>/unit.json. */
export interface WorkUnit {
  id: string;
  title: string;
  statement_informal: string;
  domain?: string;
  claim_kind: ClaimKind;
  targets: Backend[];
  prompt_template: string;
  references?: string[];
  /** Per-backend status, e.g. { rocq: "open", lean: "open" }. */
  status: Partial<Record<Backend, UnitStatus>>;
}

/** What dispatch() hands a contributor: enough to fetch the prompt + seed. */
export interface WorkUnitRef {
  unitId: string;
  backend: Backend;
  title: string;
  /** Path (in-repo) to the ready-to-paste prompt. */
  promptPath: string;
}

/** A candidate proof submitted by a contributor. Source text ONLY —
 *  never any credential, token, or account identifier. */
export interface Submission {
  unitId: string;
  backend: Backend;
  /** The full proof-assistant source the contributor's LLM produced. */
  source: string;
}

/** The verifier's machine-readable verdict. */
export interface Verdict {
  accepted: boolean;
  reason: string;
}
