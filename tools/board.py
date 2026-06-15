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
CONJ = ROOT / "tools" / "conjecture" / "results"
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
    # artifact path (repo-relative) -> the verify-track unit that proves its mean
    twin = {}
    total = verified = 0
    for d in sorted(WU.iterdir()):
        uj = d / "unit.json"
        if not uj.is_dir() and uj.exists():
            unit = json.loads(uj.read_text(encoding="utf-8"))
            art = unit.get("conjecture_artifact") or (unit.get("analysis") or {}).get("conjecture_artifact")
            if art:
                twin[art] = {"unit": unit["id"], "expected_theorem": unit.get("expected_theorem", "")}
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
                "domain": unit.get("domain", ""),
                "claim_kind": unit.get("claim_kind", ""),
                "expected_theorem": unit.get("expected_theorem", ""),
                "cost_model": unit.get("cost_model", {}),
                "targets": targets, "status": status,
                "has_decomposition": dec.exists(),
            })
    leaf_jobs = []
    for uid, dc in decomps.items():
        for l in dc.get("leaves", []):
            leaf_jobs.append({
                "theorem": dc.get("theorem", ""), "unit": uid, "id": l["id"],
                "difficulty": l.get("difficulty", 0), "depends_on": l.get("depends_on", []),
            })
    leaf_jobs.sort(key=lambda j: (j["difficulty"], j["unit"], j["id"]))
    conjectures = []
    if CONJ.is_dir():
        for f in sorted(CONJ.glob("*.json")):
            r = json.loads(f.read_text(encoding="utf-8"))
            rel = f"tools/conjecture/results/{f.name}"
            ld = r.get("limit_distribution") or {}
            conjectures.append({
                "kind": r.get("kind", "distribution"),
                "algorithm": r.get("algorithm", f.stem),
                "summand": r.get("summand", ""),
                "mean_closed_form": r.get("conjectured_mean_closed_form", ""),
                "certificate": r.get("certificate", ""),
                "certificate_verified": r.get("certificate_verified"),
                "limit": ld.get("law", ""),
                "ks": ld,
                "ks_normal": ld.get("ks_normal"),
                "ks_uniform": ld.get("ks_uniform"),
                "histogram": r.get("histogram_at_limit_n", ""),
                "artifact": rel,
                "twin": twin.get(rel),
            })
    # aggregate breakdowns for the at-a-glance summary
    from collections import Counter
    domains = Counter(u["domain"] for u in units if u["domain"])
    kinds = Counter(u["claim_kind"] for u in units if u["claim_kind"])
    # a unit is "rocq-verified" if its rocq target is verified (the anchor backend)
    rocq_verified = sum(1 for u in units if u["status"].get("rocq") == "verified")
    return {
        "repo": OWNER_REPO, "backends": BACKENDS, "units": units,
        "open_jobs": open_jobs, "decompositions": decomps, "leaf_jobs": leaf_jobs,
        "conjectures": conjectures,
        "domains": sorted(domains.items(), key=lambda kv: -kv[1]),
        "claim_kinds": sorted(kinds.items(), key=lambda kv: -kv[1]),
        "stats": {"targets": total, "verified": verified, "open": total - verified,
                  "leaves": len(leaf_jobs), "units": len(units),
                  "rocq_verified": rocq_verified},
    }


PAGE = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1"/>
<title>analysis@home — machine-checked algorithm analysis</title>
<meta name="description" content="A crowdsourced corpus of kernel-verified theorems about algorithm correctness AND cost. Bring your own LLM, prove an open job, the proof assistant re-checks every line. Verified, not trusted."/>
<style>
:root{color-scheme:light dark; --accent:#3fa34d; --line:#8884}
*{box-sizing:border-box}
body{font:16px/1.6 system-ui,sans-serif;max-width:960px;margin:0 auto;padding:1.5rem 1rem 4rem}
a{color:#2a7ae2}
h1{margin:.2rem 0;font-size:2rem}
h2{margin:2rem 0 .4rem;border-bottom:1px solid var(--line);padding-bottom:.25rem}
.tag{font-size:1.15rem;color:#777;margin:.1rem 0 .8rem}
.lead{font-size:1.03rem;max-width:66ch}
.cta{display:inline-block;margin:.4rem .4rem .2rem 0;padding:.55rem .95rem;border-radius:8px;font-weight:600;text-decoration:none}
.cta.primary{background:var(--accent);color:#fff}
.cta.ghost{border:1px solid var(--line);color:inherit}
.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:.6rem;margin:1.1rem 0 .4rem}
.card{border:1px solid var(--line);border-radius:10px;padding:.7rem .5rem;text-align:center}
.card b{display:block;font-size:1.8rem;line-height:1.1;color:var(--accent)}
.card span{font-size:.78rem;color:#888}
.bar{height:9px;background:#0002;border-radius:5px;overflow:hidden;margin:.5rem 0}
.bar>i{display:block;height:100%;background:var(--accent)}
.steps{display:grid;grid-template-columns:repeat(auto-fit,minmax(210px,1fr));gap:.6rem;margin:.6rem 0}
.step{border:1px solid var(--line);border-radius:10px;padding:.7rem .8rem}
.step b{color:var(--accent)}
.callout{border-left:3px solid var(--accent);padding:.3rem .9rem;margin:.7rem 0;background:rgba(63,163,77,.08);border-radius:0 6px 6px 0}
.chips{margin:.3rem 0 .6rem}
.chip2{display:inline-block;margin:.15rem;padding:.2rem .6rem;border:1px solid var(--line);border-radius:14px;font-size:.86em}
.chip2 b{color:var(--accent)}
table{border-collapse:collapse;width:100%;margin:.5rem 0;font-size:.92em}
th,td{border:1px solid var(--line);padding:.25rem .5rem;text-align:center}
th:first-child,td:first-child{text-align:left}
.ok{color:var(--accent);font-weight:700}.open{color:#e09b00}
.job{border:1px solid var(--line);border-radius:8px;padding:.6rem .8rem;margin:.5rem 0}
.job h3{margin:.1rem 0;font-size:1rem}
.chip{display:inline-block;font-size:.78em;padding:.05rem .4rem;border:1px solid var(--line);border-radius:6px;margin-left:.3rem;color:#888}
button,a.btn{font:inherit;padding:.35rem .7rem;border:1px solid var(--line);border-radius:6px;background:none;cursor:pointer;text-decoration:none;color:inherit}
pre{background:#0001;padding:.6rem;border-radius:6px;overflow:auto;white-space:pre-wrap;max-height:340px;font-size:.85em}
details{margin:.5rem 0;border:1px solid var(--line);border-radius:8px;padding:.35rem .7rem}
details>summary{cursor:pointer;font-weight:600}
.note{font-size:.88em;color:#888}
.leaf{display:inline-block;margin:.12rem;padding:.15rem .45rem;border:1px solid var(--line);border-radius:6px;font-size:.85em}
.leaf.good{border-color:var(--accent);color:var(--accent)}
#mfilter{font:inherit;padding:.35rem .55rem;border:1px solid var(--line);border-radius:6px;width:100%;max-width:340px;margin:.3rem 0}
</style></head><body>

<h1>analysis@home</h1>
<p class="tag"><b>Spare AI, turned into proven math.</b></p>
<p class="lead">A crowdsourced corpus of <b>machine-checked theorems about algorithms</b> —
not just that they're correct, but <b>how fast they run</b>: worst-, best- and
average-case cost, even the limiting distribution. Every proof is re-checked line
by line by a proof-assistant <b>kernel</b> (Rocq/Coq, Lean, Agda, Isabelle). Bring
your own LLM, prove an open job, open a PR — CI runs the kernel.
<b>Verified, not trusted.</b></p>
<p>
  <a class="cta primary" href="#contribute">Contribute a proof →</a>
  <a class="cta ghost" id="cta-repo" href="#">GitHub repo</a>
</p>

<div class="cards" id="cards"></div>
<div class="bar"><i id="pbar" style="width:0%"></i></div>
<p class="note"><span id="pv">0</span>/<span id="pt">0</span> backend targets
kernel-verified across <span id="pb">4</span> proof assistants.</p>

<h2>How it works (30 seconds)</h2>
<div class="steps">
  <div class="step"><b>1 · Pick a job.</b> An open theorem about an algorithm's cost
    or correctness, with a ready-to-paste prompt.</div>
  <div class="step"><b>2 · Prove it.</b> Paste the prompt into your own LLM
    (Claude, …); take the proof it returns.</div>
  <div class="step"><b>3 · Kernel checks.</b> Open a PR. CI runs the proof assistant;
    if every line holds it's merged and you're credited.</div>
</div>
<div class="callout">The server never runs an LLM and never sees your credentials.
The <b>kernel</b> does the believing — so anyone (or anything) can contribute and
nobody has to be trusted.</div>

<h2>What's proven so far</h2>
<p class="note">By cost claim:</p>
<div class="chips" id="kinds"></div>
<p class="note">By area:</p>
<div class="chips" id="domains"></div>
<p class="note">Spanning sorting &amp; searching, divide-and-conquer recurrences (the
master-theorem regimes), graph algorithms (BFS/DFS <code>O(V+E)</code>, shortest-path
relaxation), data structures (AVL, union-by-rank), number theory, and many
summation identities — all kernel-verified.</p>

<h2>Two tracks: compute, then prove</h2>
<p class="note">The <b>conjecture track</b> (pure-Python computer algebra + exhaustive
enumeration) <i>computes</i> the cost distribution and its limiting law — fast, but
<b>not trusted</b>. The <b>verify track</b> promotes the provable part (the exact
mean) to a kernel-checked theorem. <span id="twoex"></span></p>
<details><summary>Computed distributions &amp; limit laws (not trusted)</summary>
  <div id="conjectures"></div>
</details>

<h2 id="contribute">Pick an open job</h2>
<p class="note">Each is a port of a kernel-verified theorem to another proof
assistant. Copy the prompt into your LLM, then <b>Create a PR</b>. Showing the
first 30 of <span id="ojc">0</span> open jobs.</p>
<div id="jobs"></div>

<h2>Full verification matrix</h2>
<input id="mfilter" placeholder="filter units…  (e.g. quicksort, graph, fibonacci)"/>
<details><summary>Show all <span id="uc">0</span> units &times; 4 backends</summary>
  <div id="matrix"></div>
</details>

<details><summary>Bite-sized leaves (good first contributions) — <span id="lc">0</span></summary>
  <p class="note">Hard theorems are split into small, independently kernel-checked
  <b>leaves</b> (★ = difficulty, green = ★1–2).</p>
  <div id="leaves"></div>
  <div id="decomp"></div>
</details>

<p class="note" style="margin-top:2rem">Contributions licensed Apache-2.0 (code) /
CC-BY-4.0 (proofs). Repo: <a id="repolink" href="#">github.com/<span id="reponame"></span></a>.</p>

<script>
const E=(t,p={},...k)=>{const e=document.createElement(t);Object.assign(e,p);for(const c of k)e.append(c);return e};
fetch('data.json').then(r=>r.json()).then(D=>{
  const repo='https://github.com/'+D.repo;
  for(const id of ['cta-repo','repolink']) document.getElementById(id).href=repo;
  reponame.textContent=D.repo;
  const s=D.stats;
  pv.textContent=s.verified; pt.textContent=s.targets; pb.textContent=D.backends.length;
  pbar.style.width=(s.targets?100*s.verified/s.targets:0)+'%';

  // at-a-glance stat cards
  const pct=s.targets?Math.round(100*s.verified/s.targets):0;
  [[s.units,'verified units'],[s.rocq_verified,'Rocq-checked'],[pct+'%','targets verified'],
   [s.open,'open jobs'],[(D.domains||[]).length,'areas']
  ].forEach(([n,l])=>document.getElementById('cards').append(
    E('div',{className:'card'}, E('b',{textContent:String(n)}), E('span',{textContent:l}))));

  // coverage chips
  const KL={'worst-case':'worst case','best-case':'best case','expected-cost':'average (proven)',
    'complexity':'complexity','closed-form':'closed form','correctness':'correctness',
    'distribution':'distribution','limit-law':'limit law'};
  (D.claim_kinds||[]).forEach(([k,n])=>kinds.append(
    E('span',{className:'chip2'}, E('b',{textContent:n+' '}), document.createTextNode(KL[k]||k))));
  (D.domains||[]).forEach(([k,n])=>domains.append(
    E('span',{className:'chip2'}, E('b',{textContent:n+' '}), document.createTextNode(k))));

  // two-track concrete example
  const ls=(D.conjectures||[]).find(c=>/linear-search/.test(c.algorithm));
  if(ls&&ls.twin) twoex.textContent='For example, for linear search the conjecture track computes E[cost] = '
    +ls.mean_closed_form+' with a '+ls.limit+' limit; the verified twin '+ls.twin.expected_theorem+' proves the mean exactly.';

  // conjecture track
  const cj = D.conjectures || [];
  if(!cj.length) conjectures.append(E('p',{className:'note',textContent:'(none yet)'}));
  cj.forEach(c=>{
    const box=E('div',{className:'job'});
    box.append(E('h3',{}, document.createTextNode(c.algorithm),
      E('span',{className:'chip',textContent:'CONJECTURE'}),
      E('span',{className:'chip',textContent:c.kind})));
    if(c.kind==='distribution'){
      box.append(E('p',{className:'note'}, document.createTextNode('E[cost(n)] ≈ '), E('b',{textContent:c.mean_closed_form})));
      const bestKey='ks_'+(c.limit||'').split(' ')[0].toLowerCase();
      const bestKs=(c.ks||{})[bestKey];
      box.append(E('p',{className:'note'}, document.createTextNode('limit law (standardized): '),
        E('b',{textContent:c.limit}),
        document.createTextNode(bestKs!=null?'  (KS '+bestKs+'; normal='+c.ks_normal+', uniform='+c.ks_uniform+')':'')));
    } else {
      if(c.summand) box.append(E('p',{className:'note',textContent:c.summand}));
      box.append(E('p',{className:'note'}, document.createTextNode('closed form: '), E('b',{textContent:c.mean_closed_form})));
    }
    if(c.certificate){
      const v = c.certificate_verified===false ? ' ✗' : ' ✓';
      box.append(E('p',{className:'note'}, document.createTextNode('certificate: '),
        E('code',{textContent:c.certificate}), document.createTextNode(v)));
    }
    if(c.twin){
      box.append(E('p',{className:'note'}, document.createTextNode('verified twin: kernel-checked via '),
        E('code',{textContent:c.twin.expected_theorem}),
        document.createTextNode(' (unit '+c.twin.unit+')')));
    } else {
      box.append(E('p',{className:'note',textContent:'no verified twin yet — a candidate theorem to prove'}));
    }
    if(c.histogram){
      const det=E('details',{}, E('summary',{textContent:'show distribution'}), E('pre',{textContent:c.histogram}));
      box.append(det);
    }
    conjectures.append(box);
  });

  // open jobs
  ojc.textContent=D.open_jobs.length;
  if(!D.open_jobs.length) jobs.append(E('p',{textContent:'Everything is verified. 🎉'}));
  D.open_jobs.slice(0,30).forEach(j=>{
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

  // full verification matrix
  uc.textContent=s.units;
  const SY={verified:['✓','ok'],open:['·','open']};
  const tbl=E('table'); const thead=E('tr',{}, E('th',{textContent:'unit'}));
  D.backends.forEach(b=>thead.append(E('th',{textContent:b})));
  tbl.append(thead);
  D.units.forEach(u=>{
    const tags=(u.title+' '+u.id+' '+u.domain+' '+u.claim_kind+' '+u.expected_theorem).toLowerCase();
    const tr=E('tr',{'data-name':tags});
    tr.append(E('td',{}, document.createTextNode(u.title),
      E('span',{className:'chip',textContent:u.claim_kind})));
    D.backends.forEach(b=>{
      const td=E('td');
      if(!(u.targets||[]).includes(b)){ td.textContent='–'; td.className='note'; }
      else { const v=u.status[b]==='verified'; const [sym,cls]=v?SY.verified:SY.open;
        td.textContent=sym; td.className=cls; }
      tr.append(td);
    });
    tbl.append(tr);
  });
  matrix.append(tbl);
  mfilter.addEventListener('input',()=>{
    const q=mfilter.value.toLowerCase().trim();
    let shown=0;
    tbl.querySelectorAll('tr[data-name]').forEach(tr=>{
      const hit=!q||tr.getAttribute('data-name').includes(q);
      tr.style.display=hit?'':'none'; if(hit)shown++;
    });
    uc.textContent=q?shown+' / '+s.units:s.units;
  });

  // bite-sized leaves (good first)
  const lj = D.leaf_jobs || [];
  document.getElementById('lc').textContent = lj.length;
  lj.forEach(j=>{
    const t = 'in '+j.theorem + (j.depends_on.length ? ('  — needs '+j.depends_on.join(', ')) : '');
    leaves.append(E('span',{className:'leaf'+(j.difficulty<=2?' good':''),title:t,textContent:j.id+' ★'+j.difficulty}));
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
