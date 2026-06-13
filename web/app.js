// analysis@home web MVP — talks to the coordinator (coordinator/src/server.ts).
//
// Flow: list open work units -> show the ready-to-paste prompt for the chosen
// one -> POST the proof the contributor's own LLM produced -> the server
// re-checks it with the kernel and returns a verdict.
//
// Trustless invariant: this page never asks for an API key and never calls an
// LLM. It only ships proof SOURCE to the verifier.

const $ = (id) => document.getElementById(id);
let current = null; // { unitId, backend }

async function api(path, opts) {
  const res = await fetch(path, opts);
  if (!res.ok) throw new Error(`${path} -> ${res.status}`);
  return res.json();
}

async function loadUnits() {
  const sel = $("unit");
  let open;
  try {
    open = await api("/api/units");
  } catch {
    sel.innerHTML = "<option>(start the coordinator: npm --prefix coordinator start)</option>";
    $("prompt").textContent = "No coordinator. Run: node coordinator/src/server.ts, then reload.";
    return;
  }
  if (!open.length) {
    sel.innerHTML = "<option>(no open units — all verified 🎉)</option>";
    $("prompt").textContent = "Every target is verified.";
    return;
  }
  sel.innerHTML = "";
  for (const u of open) {
    const o = document.createElement("option");
    o.value = `${u.unitId}::${u.backend}`;
    o.textContent = `[${u.backend}] ${u.title} (${u.status})`;
    sel.appendChild(o);
  }
  sel.onchange = () => selectUnit(sel.value);
  await selectUnit(sel.value);
}

async function selectUnit(value) {
  const [unitId, backend] = value.split("::");
  current = { unitId, backend };
  $("prompt").textContent = "Loading prompt…";
  try {
    const { prompt, expected_theorem } = await api(`/api/prompt?unit=${encodeURIComponent(unitId)}`);
    $("prompt").textContent = prompt;
    $("thm").textContent = expected_theorem ?? "—";
  } catch (e) {
    $("prompt").textContent = `Could not load prompt: ${e.message}`;
  }
}

$("copy").addEventListener("click", async () => {
  await navigator.clipboard.writeText($("prompt").textContent);
  $("copy").textContent = "Copied!";
  setTimeout(() => ($("copy").textContent = "Copy prompt"), 1500);
});

$("submit").addEventListener("click", async () => {
  const out = $("verdict");
  const source = $("submission").value.trim();
  if (!current) { out.textContent = "Pick a work unit first."; return; }
  if (!source) { out.textContent = "Paste a proof first."; return; }
  out.textContent = "Verifying with the kernel…";
  try {
    const v = await api("/api/submit", {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ unitId: current.unitId, backend: current.backend, source }),
    });
    out.textContent = (v.accepted ? "✅ verified — " : "❌ rejected — ") + v.reason;
    if (v.accepted) loadUnits(); // refresh: the unit drops off the open list
  } catch (e) {
    out.textContent = `Error: ${e.message}`;
  }
});

loadUnits();
