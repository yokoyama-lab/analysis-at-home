// analysis@home web MVP — STUB.
//
// Shows a ready-to-paste prompt and accepts a pasted proof for verification.
// Phase 1 wires `loadPrompt` / `verify` to the coordinator + verifier behind a
// minimal backend. For now they are mocked so the page is usable offline.
//
// Trustless invariant: this page never asks for an API key and never calls an
// LLM. It only ships proof SOURCE to the verifier.

const WORK_UNIT = "insertion-sort-comparisons";
const BACKEND = "rocq";

// TODO (Phase 1): GET /api/dispatch -> { promptPath }, then fetch its contents.
async function loadPrompt() {
  const path = `../work-units/${WORK_UNIT}/prompt-template.md`;
  try {
    const res = await fetch(path);
    if (!res.ok) throw new Error(String(res.status));
    return await res.text();
  } catch {
    return `(Could not load ${path}. Open it directly in the repo and copy the prompt.)`;
  }
}

// TODO (Phase 1): POST /api/submit { unitId, backend, source } -> Verdict.
// The server shells out to verifier/verify.sh in a sandbox. Mocked here.
async function verify(source) {
  if (/\b(Admitted|admit|Axiom|sorry)\b/.test(source)) {
    return { accepted: false, reason: "contains Admitted/admit/Axiom/sorry" };
  }
  return {
    accepted: false,
    reason: "verification backend not wired yet (Phase 1) — run verifier/verify.sh locally",
  };
}

const $ = (id) => document.getElementById(id);

loadPrompt().then((text) => { $("prompt").textContent = text; });

$("copy").addEventListener("click", async () => {
  await navigator.clipboard.writeText($("prompt").textContent);
  $("copy").textContent = "Copied!";
  setTimeout(() => ($("copy").textContent = "Copy prompt"), 1500);
});

$("submit").addEventListener("click", async () => {
  const source = $("submission").value.trim();
  const out = $("verdict");
  if (!source) { out.textContent = "Paste a proof first."; return; }
  out.textContent = "Verifying…";
  const v = await verify(source);
  out.textContent = (v.accepted ? "✅ verified — " : "❌ rejected — ") + v.reason;
});
