#!/usr/bin/env python3
"""Generate the static contribution board (site/) from the repo.

Scans work-units/*/unit.json (+ decomposition/leaves.json) and emits:
  site/data.json   machine-readable snapshot
  site/index.html  a self-contained dashboard: verification matrix, the OPEN
                   jobs to claim (with the ready-to-paste prompt and a
                   "create a PR" deep link), the decomposition showcase, and a
                   5-minute how-to-contribute.

No server needed: this is published on GitHub Pages; the kernel check happens in
CI when a contributor opens a PR. Run locally:  python3 tools/board.py
"""
from __future__ import annotations
import json, html, pathlib, re

ROOT = pathlib.Path(__file__).resolve().parent.parent
WU = ROOT / "work-units"
SITE = ROOT / "site"
OWNER_REPO = "yokoyama-lab/analysis-at-home"
BRANCH = "main"
BACKENDS = ["rocq", "lean", "agda", "isabelle"]
NEWFILE = {  # where a new submission of each backend lands
    "rocq": ("targets/rocq", "Proof.v"),
    "lean": ("targets/lean", "Proof.lean"),
    "agda": ("targets/agda", "Submission.agda"),
    "isabelle": ("targets/isabelle", "Submission.thy"),
}


def read_prompt(unit_dir: pathlib.Path, unit: dict) -> str:
    p = unit_dir / unit.get("prompt_template", "prompt-template.md")
    if not p.exists():
        return ""
    txt = p.read_text(encoding="utf-8")
    txt = re.sub(r"<!--.*?-->", "", txt, flags=re.S)  # drop the HTML comment
    return txt.strip()


def pr_url(unit_id: str, backend: str) -> str:
    sub, fname = NEWFILE[backend]
    path = f"work-units/{unit_id}/{sub}/{fname}"
    return f"https://github.com/{OWNER_REPO}/new/{BRANCH}?filename={path}"


def collect() -> dict:
    units, open_jobs, decomps = [], [], {}
    total = verified = 0
    for d in sorted(WU.iterdir()):
        uj = d / "unit.json"
        if not uj.is_dir() and uj.exists():
            unit = json.loads(uj.read_text(encoding="utf-8"))
            status = unit.get("status", {})
            targets = unit.get("targets", [])
            for b in targets:
                total += 1
                if status.get(b) == "verified":
                    verified += 1
                else:
                    open_jobs.append({
                        "unit": unit["id"], "title": unit["title"], "backend": b,
                        "claim_kind": unit.get("claim_kind", ""),
                        "expected_theorem": unit.get("expected_theorem", ""),
                        "prompt": read_prompt(d, unit),
                        "pr_url": pr_url(unit["id"], b),
                    })
            dec = d / "decomposition" / "leaves.json"
            if dec.exists():
                decomps[unit["id"]] = json.loads(dec.read_text(encoding="utf-8"))
            units.append({
                "id": unit["id"], "title": unit["title"],
                "claim_kind": unit.get("claim_kind", ""),
                "expected_theorem": unit.get("expected_theorem", ""),
                "cost_model": unit.get("cost_model", {}),
                "targets": targets, "status": status,
                "has_decomposition": dec.exists(),
            })
    return {
        "repo": OWNER_REPO, "backends": BACKENDS, "units": units,
        "open_jobs": open_jobs, "decompositions": decomps,
        "stats": {"targets": total, "verified": verified, "open": total - verified},
    }


PAGE = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1"/>
<title>analysis@home — contribute a proof</title>
<style>
:root{color-scheme:light dark}
*{box-sizing:border-box}
body{font:16px/1.6 system-ui,sans-serif;max-width:920px;margin:2rem auto;padding:0 1rem}
h1{margin:.2rem 0}.tag{color:#888;margin:.2rem 0 1rem}
.bar{height:10px;background:#0002;border-radius:5px;overflow:hidden;margin:.4rem 0}
.bar>i{display:block;height:100%;background:#4caf50}
table{border-collapse:collapse;width:100%;margin:.5rem 0}
th,td{border:1px solid #8883;padding:.3rem .5rem;text-align:center}
th:first-child,td:first-child{text-align:left}
.ok{color:#4caf50;font-weight:700}.open{color:#e09b00}
.job{border:1px solid #8884;border-radius:8px;padding:.6rem .8rem;margin:.5rem 0}
.job h3{margin:.1rem 0}.chip{display:inline-block;font-size:.8em;padding:.05rem .4rem;border:1px solid #8886;border-radius:6px;margin-left:.3rem}
button,a.btn{font:inherit;padding:.35rem .7rem;border:1px solid #8886;border-radius:6px;background:none;cursor:pointer;text-decoration:none;color:inherit}
pre{background:#0001;padding:.6rem;border-radius:6px;overflow:auto;white-space:pre-wrap;max-height:340px;font-size:.85em}
details{margin:.3rem 0}.note{font-size:.85em;color:#888}
.leaf{display:inline-block;margin:.12rem;padding:.15rem .45rem;border:1px solid #8884;border-radius:6px;font-size:.85em}
</style></head><body>
<h1>analysis@home</h1>
<p class="tag"><b>Spare AI, turned into proven math.</b> Pick an open job, prove
it with your own LLM, open a PR — the kernel re-checks every line. <i>Verified,
not trusted.</i></p>

<h2>Progress</h2>
<p><b id="pv">0</b>/<b id="pt">0</b> backend targets kernel-verified
(<span id="po">0</span> open).</p>
<div class="bar"><i id="pbar" style="width:0%"></i></div>

<h2>Verification matrix</h2>
<div id="matrix"></div>

<h2>Open jobs — pick one</h2>
<p class="note">Each is a port of a proven theorem to another proof assistant.
Copy the prompt into your own LLM (Claude, …), then <b>Create a PR</b> with the
result. Locally you can self-check first:
<code>verifier/verify.sh &lt;backend&gt; &lt;file&gt; &lt;theorem&gt;</code>.</p>
<div id="jobs"></div>

<h2>How decomposition works</h2>
<p class="note">Hard theorems are split into small, independently kernel-checked
<b>leaves</b> (★ = difficulty). Many small proofs assemble into the whole — see
these examples.</p>
<div id="decomp"></div>

<h2>Contribute in 5 minutes</h2>
<ol>
<li>Pick an open job above and copy its prompt.</li>
<li>Paste it into your own LLM; take the proof it returns.</li>
<li>Click <b>Create a PR</b>, paste the proof, propose the change. CI runs the
kernel; if it holds, a maintainer merges it and you're credited.</li>
</ol>
<p class="note">Credentials never leave your machine. Your contribution is
licensed Apache-2.0 (code) / CC-BY-4.0 (proofs).
Repo: <a id="repolink" href="#">GitHub</a>.</p>

<script>
const E=(t,p={},...k)=>{const e=document.createElement(t);Object.assign(e,p);for(const c of k)e.append(c);return e};
fetch('data.json').then(r=>r.json()).then(D=>{
  const repo='https://github.com/'+D.repo;
  document.getElementById('repolink').href=repo;
  const s=D.stats;
  pv.textContent=s.verified;pt.textContent=s.targets;po.textContent=s.open;
  pbar.style.width=(s.targets?100*s.verified/s.targets:0)+'%';

  // matrix
  const tbl=E('table');
  const head=E('tr',{}, E('th',{textContent:'unit'}));
  D.backends.forEach(b=>head.append(E('th',{textContent:b})));
  tbl.append(head);
  D.units.forEach(u=>{
    const tr=E('tr',{}, E('td',{}, E('span',{textContent:u.title})));
    D.backends.forEach(b=>{
      const has=u.targets.includes(b);
      const v=u.status[b]==='verified';
      tr.append(E('td',{className:v?'ok':(has?'open':''),textContent:v?'✓':(has?'open':'—')}));
    });
    tbl.append(tr);
  });
  matrix.append(tbl);

  // open jobs
  if(!D.open_jobs.length) jobs.append(E('p',{textContent:'Everything is verified. 🎉'}));
  D.open_jobs.forEach(j=>{
    const box=E('div',{className:'job'});
    box.append(E('h3',{}, document.createTextNode(j.title),
      E('span',{className:'chip',textContent:'['+j.backend+']'}),
      E('span',{className:'chip',textContent:j.claim_kind})));
    box.append(E('p',{className:'note',textContent:'prove: '+j.expected_theorem}));
    const det=E('details',{}, E('summary',{textContent:'show prompt'}), E('pre',{textContent:j.prompt||'(see the unit prompt-template)'}));
    box.append(det);
    const row=E('p');
    row.append(E('button',{textContent:'Copy prompt',onclick:()=>{navigator.clipboard.writeText(j.prompt);}}));
    row.append(document.createTextNode(' '));
    row.append(E('a',{className:'btn',href:j.pr_url,target:'_blank',rel:'noopener',textContent:'Create a PR →'}));
    box.append(row);
    jobs.append(box);
  });

  // decompositions
  for(const [uid,dc] of Object.entries(D.decompositions)){
    const box=E('div',{className:'job'});
    box.append(E('h3',{textContent:dc.theorem}));
    const wrap=E('div');
    (dc.leaves||[]).forEach(l=>wrap.append(E('span',{className:'leaf',textContent:l.id+' ★'+l.difficulty})));
    box.append(wrap);
    decomp.append(box);
  }
});
</script>
</body></html>
"""


def main() -> None:
    data = collect()
    SITE.mkdir(exist_ok=True)
    (SITE / "data.json").write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    (SITE / "index.html").write_text(PAGE, encoding="utf-8")
    s = data["stats"]
    print(f"site/ generated: {len(data['units'])} units, {s['verified']}/{s['targets']} verified, "
          f"{len(data['open_jobs'])} open jobs, {len(data['decompositions'])} decompositions")


if __name__ == "__main__":
    main()
