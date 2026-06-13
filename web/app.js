// analysis@home web MVP — talks to the coordinator (coordinator/src/server.ts).
//
// Two ways to contribute, both kernel-checked, both credential-free:
//   - whole-theorem units (the selector + prompt below), and
//   - LEAVES of a decomposed theorem (the panel up top): prove one small lemma
//     by returning just the proof script; many leaves assemble into the whole.

const $ = (id) => document.getElementById(id);
let current = null; // {kind:'theorem',unitId,backend} | {kind:'leaf',unit,leaf}
let decompUnit = null;

async function api(path, opts) {
  const res = await fetch(path, opts);
  if (!res.ok) throw new Error(`${path} -> ${res.status}`);
  return res.json();
}

// ---------- decomposition (leaves) ----------
async function loadDecomp() {
  let ds;
  try { ds = await api("/api/decompositions"); } catch { $("decomp").style.display = "none"; return; }
  if (!ds.length) { $("decomp").style.display = "none"; return; }
  decompUnit = ds[0].unitId;
  $("dtitle").textContent = ds[0].theorem;
  const { verified, total, leaves } = await api(`/api/leaves?unit=${encodeURIComponent(decompUnit)}`);
  $("prog").textContent = `${verified}/${total}`;
  $("progbar").style.width = `${total ? (100 * verified) / total : 0}%`;
  const box = $("leaves");
  box.innerHTML = "";
  for (const l of leaves) {
    const b = document.createElement("button");
    b.className = "leaf" + (l.status === "verified" ? " done" : "");
    b.textContent = `${l.id} ★${l.difficulty}${l.status === "verified" ? " ✓" : ""}`;
    b.disabled = l.status === "verified" || l.blocked;
    if (l.blocked) b.title = `blocked: needs ${l.depends_on.join(", ")}`;
    b.onclick = () => selectLeaf(l.id);
    box.appendChild(b);
  }
}

async function selectLeaf(leaf) {
  current = { kind: "leaf", unit: decompUnit, leaf };
  $("prompt").textContent = "Loading leaf…";
  const { prompt, expected_theorem } = await api(
    `/api/leaf?unit=${encodeURIComponent(decompUnit)}&leaf=${encodeURIComponent(leaf)}`);
  $("prompt").textContent = prompt;
  $("thm").textContent = `${expected_theorem} (paste back ONLY the proof script)`;
  $("verdict").textContent = "";
}

// ---------- whole-theorem units ----------
async function loadUnits() {
  const sel = $("unit");
  let open;
  try { open = await api("/api/units"); }
  catch {
    sel.innerHTML = "<option>(start the coordinator: npm --prefix coordinator start)</option>";
    $("prompt").textContent = "No coordinator. Run: node coordinator/src/server.ts, then reload.";
    return;
  }
  if (!open.length) { sel.innerHTML = "<option>(no open whole-theorem units)</option>"; return; }
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
  current = { kind: "theorem", unitId, backend };
  $("prompt").textContent = "Loading prompt…";
  try {
    const { prompt, expected_theorem } = await api(`/api/prompt?unit=${encodeURIComponent(unitId)}`);
    $("prompt").textContent = prompt;
    $("thm").textContent = expected_theorem ?? "—";
  } catch (e) { $("prompt").textContent = `Could not load prompt: ${e.message}`; }
}

// ---------- shared controls ----------
$("copy").addEventListener("click", async () => {
  await navigator.clipboard.writeText($("prompt").textContent);
  $("copy").textContent = "Copied!";
  setTimeout(() => ($("copy").textContent = "Copy prompt"), 1500);
});

$("submit").addEventListener("click", async () => {
  const out = $("verdict");
  const source = $("submission").value.trim();
  if (!current) { out.textContent = "Pick a work unit or a leaf first."; return; }
  if (!source) { out.textContent = "Paste a proof first."; return; }
  out.textContent = "Verifying with the kernel…";
  try {
    let v;
    if (current.kind === "leaf") {
      v = await api("/api/submit-leaf", {
        method: "POST", headers: { "content-type": "application/json" },
        body: JSON.stringify({ unit: current.unit, leaf: current.leaf, source }),
      });
    } else {
      v = await api("/api/submit", {
        method: "POST", headers: { "content-type": "application/json" },
        body: JSON.stringify({ unitId: current.unitId, backend: current.backend, source }),
      });
    }
    out.textContent = (v.accepted ? "✅ verified — " : "❌ rejected — ") + v.reason;
    if (v.accepted) { loadDecomp(); loadUnits(); }
  } catch (e) { out.textContent = `Error: ${e.message}`; }
});

loadDecomp();
loadUnits();
