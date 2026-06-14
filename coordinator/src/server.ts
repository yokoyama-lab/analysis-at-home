// analysis@home coordinator — minimal HTTP server wiring the web MVP to the
// kernel verifier. Runs on Node >= 22.6 (native TypeScript), no dependencies:
//
//   node coordinator/src/server.ts        # then open http://localhost:8787
//
// Trustless invariants enforced here:
//   - this server NEVER calls an LLM and NEVER receives credentials; submissions
//     are proof SOURCE only;
//   - acceptance is decided ONLY by verifier/verify.sh (a proof-assistant
//     kernel), never by this process.
//
// Two flavours of work:
//   - whole-theorem units (work-units/<id>/unit.json), and
//   - decomposed units: a unit dir with decomposition/leaves.json is served as
//     many small LEAF jobs. A leaf submission is just the proof script (the
//     tactics); the server wraps it in the canonical lemma statement, so the
//     statement is fixed for free (signature-equivalence), and verifies it
//     against spec + the already-verified dependency proofs. Progress is k/N.

import { createServer, type IncomingMessage, type ServerResponse } from "node:http";
import { readFile, readdir, writeFile, mkdtemp, rm, access } from "node:fs/promises";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { join, dirname } from "node:path";
import { tmpdir } from "node:os";
import { fileURLToPath } from "node:url";
import type { WorkUnit, Submission, Verdict, Backend } from "./types.js";

const execFileP = promisify(execFile);
const HERE = dirname(fileURLToPath(import.meta.url));
const REPO = join(HERE, "..", "..");
const WORK_UNITS = join(REPO, "work-units");
const WEB = join(REPO, "web");
const VERIFY = join(REPO, "verifier", "verify.sh");
const PORT = Number(process.env.PORT ?? 8787);
// Runtime ledger (gitignored): verified statuses + per-leaf attempts survive
// restart. A leaf that fails this many times without success is flagged
// needs_split (adaptive grain: too big a job — decompose it further).
const LEDGER = join(REPO, "coordinator", "ledger.json");
const SPLIT_THRESHOLD = Number(process.env.AAH_SPLIT_THRESHOLD ?? 3);

type UnitRec = WorkUnit & { dir: string; expected_theorem?: string };
const units = new Map<string, UnitRec>();

type LeafRec = { id: string; difficulty: number; depends_on: string[]; header: string };
type Decomp = {
  unitId: string;
  theorem: string;
  specSrc: string;
  leaves: LeafRec[];
  status: Map<string, "open" | "verified">;
  proof: Map<string, string>; // full wrapped lemma text of a verified leaf
  attempts: Map<string, number>; // failed attempts per leaf (for adaptive split)
};
const decomps = new Map<string, Decomp>();

type Ledger = {
  units?: Record<string, Record<string, string>>;
  leaves?: Record<string, Record<string, { status?: string; attempts?: number; proof?: string }>>;
};

async function loadLedger(): Promise<void> {
  if (!(await exists(LEDGER))) return;
  let led: Ledger;
  try { led = JSON.parse(await readFile(LEDGER, "utf8")) as Ledger; } catch { return; }
  for (const [uid, backends] of Object.entries(led.units ?? {})) {
    const u = units.get(uid);
    if (u) for (const [b, st] of Object.entries(backends)) if (st === "verified") u.status[b as Backend] = "verified";
  }
  for (const [uid, leaves] of Object.entries(led.leaves ?? {})) {
    const dc = decomps.get(uid);
    if (!dc) continue;
    for (const [lid, rec] of Object.entries(leaves)) {
      if (rec.status === "verified") dc.status.set(lid, "verified");
      if (typeof rec.attempts === "number") dc.attempts.set(lid, rec.attempts);
      if (rec.proof) dc.proof.set(lid, rec.proof);
    }
  }
}

async function saveLedger(): Promise<void> {
  const led: Ledger = { units: {}, leaves: {} };
  for (const u of units.values()) {
    const v: Record<string, string> = {};
    for (const b of u.targets) if (u.status[b] === "verified") v[b] = "verified";
    if (Object.keys(v).length) led.units![u.id] = v;
  }
  for (const dc of decomps.values()) {
    const lv: Record<string, { status?: string; attempts?: number; proof?: string }> = {};
    for (const l of dc.leaves) {
      const status = dc.status.get(l.id);
      const attempts = dc.attempts.get(l.id) ?? 0;
      const proof = dc.proof.get(l.id);
      if (status === "verified" || attempts > 0) lv[l.id] = { status, attempts, ...(proof ? { proof } : {}) };
    }
    if (Object.keys(lv).length) led.leaves![dc.unitId] = lv;
  }
  await writeFile(LEDGER, JSON.stringify(led, null, 2), "utf8");
}

const exists = (p: string) => access(p).then(() => true, () => false);

// Split a leaf .v into its header (comment + `Lemma name : stmt.`) and the rest.
// The header fixes the statement; contributors only supply the proof script.
function splitProof(src: string): { header: string } {
  const m = src.search(/^\s*Proof\./m);
  return { header: m < 0 ? src : src.slice(0, m) };
}

async function loadUnits(): Promise<void> {
  for (const e of await readdir(WORK_UNITS, { withFileTypes: true })) {
    if (!e.isDirectory()) continue;
    const dir = join(WORK_UNITS, e.name);
    try {
      const unit = JSON.parse(await readFile(join(dir, "unit.json"), "utf8")) as UnitRec;
      units.set(unit.id, { ...unit, dir });
      const manifestPath = join(dir, "decomposition", "leaves.json");
      if (await exists(manifestPath)) await loadDecomp(unit.id, join(dir, "decomposition"), manifestPath);
    } catch {
      // directory without a unit.json — skip
    }
  }
}

async function loadDecomp(unitId: string, ddir: string, manifestPath: string): Promise<void> {
  const m = JSON.parse(await readFile(manifestPath, "utf8")) as {
    theorem: string; spec: string;
    leaves: { id: string; file: string; difficulty: number; depends_on: string[] }[];
  };
  const specSrc = await readFile(join(ddir, m.spec), "utf8");
  const leaves: LeafRec[] = [];
  for (const l of m.leaves) {
    const { header } = splitProof(await readFile(join(ddir, l.file), "utf8"));
    leaves.push({ id: l.id, difficulty: l.difficulty, depends_on: l.depends_on, header });
  }
  decomps.set(unitId, {
    unitId, theorem: m.theorem, specSrc, leaves,
    status: new Map(leaves.map((l) => [l.id, "open"])),
    proof: new Map(),
    attempts: new Map(leaves.map((l) => [l.id, 0])),
  });
}

// Run the kernel verifier on a complete source file; source text only.
async function verifyFile(source: string, backend: string, theorem: string): Promise<Verdict> {
  const tdir = await mkdtemp(join(tmpdir(), "aah-"));
  try {
    const file = join(tdir, "Submission.v");
    await writeFile(file, source, "utf8");
    let out = "";
    try {
      out = (await execFileP("bash", [VERIFY, backend, file, theorem],
        { timeout: 120_000, maxBuffer: 1 << 20 })).stdout;
    } catch (err) {
      out = (err as { stdout?: string }).stdout ?? "";
    }
    const line = out.trim().split("\n").pop() ?? "";
    try { return JSON.parse(line) as Verdict; }
    catch { return { accepted: false, reason: "verifier produced no verdict" }; }
  } finally {
    await rm(tdir, { recursive: true, force: true });
  }
}

// whole-theorem submit: open -> submitted -> verified, decided by the verifier.
async function submit(s: Submission): Promise<Verdict> {
  const u = units.get(s.unitId);
  if (!u) return { accepted: false, reason: `unknown unit: ${s.unitId}` };
  if (!u.targets.includes(s.backend)) return { accepted: false, reason: `backend ${s.backend} not in scope` };
  if (!u.expected_theorem) return { accepted: false, reason: "unit has no expected_theorem" };
  const prev = u.status[s.backend];
  u.status[s.backend] = "submitted";
  const verdict = await verifyFile(s.source, s.backend, u.expected_theorem);
  // do not downgrade an already-verified target on a failed attempt
  if (verdict.accepted) { u.status[s.backend] = "verified"; await saveLedger(); }
  else u.status[s.backend] = prev === "verified" ? "verified" : "open";
  return verdict;
}

function progress(dc: Decomp): { verified: number; total: number } {
  let v = 0;
  for (const st of dc.status.values()) if (st === "verified") v++;
  return { verified: v, total: dc.leaves.length };
}

// leaf submit: wrap the tactics in the canonical statement (fixes the
// statement), prepend spec + verified deps, and ask the kernel.
async function submitLeaf(unitId: string, leafId: string, tactics: string): Promise<Verdict & { progress?: object }> {
  const dc = decomps.get(unitId);
  if (!dc) return { accepted: false, reason: `no decomposition for ${unitId}` };
  const leaf = dc.leaves.find((l) => l.id === leafId);
  if (!leaf) return { accepted: false, reason: `unknown leaf: ${leafId}` };
  const missing = leaf.depends_on.filter((d) => dc.status.get(d) !== "verified");
  if (missing.length) return { accepted: false, reason: `blocked — verify dependencies first: ${missing.join(", ")}`, progress: progress(dc) };

  const wrapped = `${leaf.header}Proof.\n${tactics}\nQed.\n`;
  const deps = dc.leaves
    .filter((l) => l.id !== leafId && dc.status.get(l.id) === "verified")
    .map((l) => dc.proof.get(l.id))
    .join("\n");
  const combined = `${dc.specSrc}\n${deps}\n${wrapped}`;
  const verdict = await verifyFile(combined, "rocq", leafId);
  if (verdict.accepted) {
    dc.proof.set(leafId, wrapped);
    dc.status.set(leafId, "verified");
    dc.attempts.set(leafId, 0);
  } else {
    dc.attempts.set(leafId, (dc.attempts.get(leafId) ?? 0) + 1);
  }
  await saveLedger();
  return { ...verdict, progress: progress(dc) };
}

function send(res: ServerResponse, status: number, body: string | Buffer, type = "application/json"): void {
  res.writeHead(status, { "content-type": type });
  res.end(body);
}

function readBody(req: IncomingMessage): Promise<string> {
  return new Promise((resolve, reject) => {
    let d = "";
    req.on("data", (c) => (d += c));
    req.on("end", () => resolve(d));
    req.on("error", reject);
  });
}

const server = createServer(async (req, res) => {
  const url = new URL(req.url ?? "/", "http://localhost");
  try {
    if (req.method === "GET" && (url.pathname === "/" || url.pathname === "/index.html"))
      return send(res, 200, await readFile(join(WEB, "index.html")), "text/html; charset=utf-8");
    if (req.method === "GET" && url.pathname === "/app.js")
      return send(res, 200, await readFile(join(WEB, "app.js")), "text/javascript; charset=utf-8");

    if (req.method === "GET" && url.pathname === "/api/units") {
      const open = [...units.values()].flatMap((u) =>
        u.targets
          .filter((b) => (u.status[b] ?? "open") !== "verified")
          .map((b) => ({ unitId: u.id, backend: b, title: u.title, status: u.status[b] ?? "open" })),
      );
      return send(res, 200, JSON.stringify(open));
    }

    if (req.method === "GET" && url.pathname === "/api/prompt") {
      const u = units.get(url.searchParams.get("unit") ?? "");
      if (!u) return send(res, 404, JSON.stringify({ error: "unknown unit" }));
      return send(res, 200, JSON.stringify({
        unitId: u.id,
        prompt: await readFile(join(u.dir, u.prompt_template), "utf8"),
        expected_theorem: u.expected_theorem,
      }));
    }

    // ----- decomposition (leaf) endpoints -----
    if (req.method === "GET" && url.pathname === "/api/decompositions") {
      return send(res, 200, JSON.stringify([...decomps.values()].map((dc) => ({
        unitId: dc.unitId, theorem: dc.theorem, ...progress(dc),
      }))));
    }

    if (req.method === "GET" && url.pathname === "/api/leaves") {
      const dc = decomps.get(url.searchParams.get("unit") ?? "");
      if (!dc) return send(res, 404, JSON.stringify({ error: "no decomposition" }));
      const leaves = dc.leaves.map((l) => ({
        id: l.id, difficulty: l.difficulty, depends_on: l.depends_on,
        status: dc.status.get(l.id),
        blocked: l.depends_on.some((d) => dc.status.get(d) !== "verified"),
        attempts: dc.attempts.get(l.id) ?? 0,
        needs_split: dc.status.get(l.id) !== "verified" && (dc.attempts.get(l.id) ?? 0) >= SPLIT_THRESHOLD,
      }));
      return send(res, 200, JSON.stringify({ theorem: dc.theorem, ...progress(dc), leaves }));
    }

    if (req.method === "GET" && url.pathname === "/api/leaf") {
      const dc = decomps.get(url.searchParams.get("unit") ?? "");
      const leaf = dc?.leaves.find((l) => l.id === url.searchParams.get("leaf"));
      if (!dc || !leaf) return send(res, 404, JSON.stringify({ error: "unknown leaf" }));
      const depStubs = dc.leaves
        .filter((l) => leaf.depends_on.includes(l.id))
        .map((l) => `${l.header}Proof. Admitted.`)
        .join("\n\n");
      const prompt =
        `${dc.specSrc}\n` +
        (depStubs ? `(* --- you may assume these already-proven lemmas: --- *)\n${depStubs}\n\n` : "") +
        `(* --- Prove THIS lemma. Return ONLY the proof script (the tactics that\n` +
        `   go between Proof. and Qed.), nothing else: --- *)\n` +
        `${leaf.header}Proof.\n  (* your tactics here *)\nQed.\n`;
      return send(res, 200, JSON.stringify({ leaf: leaf.id, expected_theorem: leaf.id, difficulty: leaf.difficulty, prompt }));
    }

    if (req.method === "POST" && url.pathname === "/api/submit-leaf") {
      const b = JSON.parse(await readBody(req)) as { unit: string; leaf: string; source: string };
      return send(res, 200, JSON.stringify(await submitLeaf(b.unit, b.leaf, b.source)));
    }

    if (req.method === "POST" && url.pathname === "/api/submit") {
      const sub = JSON.parse(await readBody(req)) as Submission;
      const verdict = await submit(sub);
      return send(res, 200, JSON.stringify({ ...verdict, status: units.get(sub.unitId)?.status }));
    }

    send(res, 404, JSON.stringify({ error: "not found" }));
  } catch (e) {
    send(res, 500, JSON.stringify({ error: String((e as Error)?.message ?? e) }));
  }
});

await loadUnits();
await loadLedger();
server.listen(PORT, () => {
  // eslint-disable-next-line no-console
  console.log(`analysis@home coordinator on http://localhost:${PORT} (${units.size} units, ${decomps.size} decompositions; verifier=${VERIFY})`);
});
