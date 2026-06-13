// analysis@home coordinator — minimal HTTP server wiring the web MVP to the
// kernel verifier. Runs on Node >= 22.6 (native TypeScript), no dependencies:
//
//   node coordinator/src/server.ts        # then open http://localhost:8787
//
// Trustless invariants enforced here:
//   - this server NEVER calls an LLM and NEVER receives credentials; /api/submit
//     accepts proof SOURCE only;
//   - acceptance is decided ONLY by verifier/verify.sh (a proof-assistant
//     kernel), never by this process.
// The in-memory state machine mirrors coordinator.ts (the typed reference model).

import { createServer, type IncomingMessage, type ServerResponse } from "node:http";
import { readFile, readdir, writeFile, mkdtemp, rm } from "node:fs/promises";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { join, dirname } from "node:path";
import { tmpdir } from "node:os";
import { fileURLToPath } from "node:url";
import type { WorkUnit, Submission, Verdict } from "./types.js";

const execFileP = promisify(execFile);
const HERE = dirname(fileURLToPath(import.meta.url));
const REPO = join(HERE, "..", "..");
const WORK_UNITS = join(REPO, "work-units");
const WEB = join(REPO, "web");
const VERIFY = join(REPO, "verifier", "verify.sh");
const PORT = Number(process.env.PORT ?? 8787);

type UnitRec = WorkUnit & { dir: string; expected_theorem?: string };
const units = new Map<string, UnitRec>();

async function loadUnits(): Promise<void> {
  for (const e of await readdir(WORK_UNITS, { withFileTypes: true })) {
    if (!e.isDirectory()) continue;
    const dir = join(WORK_UNITS, e.name);
    try {
      const unit = JSON.parse(await readFile(join(dir, "unit.json"), "utf8")) as UnitRec;
      units.set(unit.id, { ...unit, dir });
    } catch {
      // directory without a unit.json — skip
    }
  }
}

// Re-check a candidate proof with the kernel. Source text only; no credentials.
async function runVerifier(s: Submission): Promise<Verdict> {
  const u = units.get(s.unitId);
  if (!u) return { accepted: false, reason: `unknown unit: ${s.unitId}` };
  if (!u.expected_theorem) return { accepted: false, reason: "unit has no expected_theorem" };
  const tdir = await mkdtemp(join(tmpdir(), "aah-"));
  try {
    const file = join(tdir, "Submission.v");
    await writeFile(file, s.source, "utf8");
    let out = "";
    try {
      out = (await execFileP("bash", [VERIFY, s.backend, file, u.expected_theorem],
        { timeout: 120_000, maxBuffer: 1 << 20 })).stdout;
    } catch (err) {
      // verify.sh exits non-zero on rejection; the JSON verdict is still on stdout
      out = (err as { stdout?: string }).stdout ?? "";
    }
    const line = out.trim().split("\n").pop() ?? "";
    try { return JSON.parse(line) as Verdict; }
    catch { return { accepted: false, reason: "verifier produced no verdict" }; }
  } finally {
    await rm(tdir, { recursive: true, force: true });
  }
}

// open -> submitted -> verified, decided only by the verifier.
async function submit(s: Submission): Promise<Verdict> {
  const u = units.get(s.unitId);
  if (!u) return { accepted: false, reason: `unknown unit: ${s.unitId}` };
  if (!u.targets.includes(s.backend)) return { accepted: false, reason: `backend ${s.backend} not in scope` };
  u.status[s.backend] = "submitted";
  const verdict = await runVerifier(s);
  u.status[s.backend] = verdict.accepted ? "verified" : "open";
  return verdict;
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
server.listen(PORT, () => {
  // eslint-disable-next-line no-console
  console.log(`analysis@home coordinator on http://localhost:${PORT} (${units.size} work units; verifier=${VERIFY})`);
});
