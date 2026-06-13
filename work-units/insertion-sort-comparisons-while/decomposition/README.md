# Decomposed proof — many small jobs, one certified theorem

This is a worked example of the project's core design: **slice one theorem into
small, independently-checkable leaves so many contributors can each finish one
small piece reliably, and the kernel assembles them into the whole.**

The theorem (`insertion_sort_while_comparisons_upper_bound`, the `while-ops`
unit) is split into a fixed shared **spec** + **10 leaf lemmas** + a short
**assembly**:

```
spec.v            shared cost model + program (fixed; contributors don't edit)
leaves/NN_*.v     ONE lemma each — the unit of work; see leaves.json for
                  difficulty (★1–4) and dependencies
main.v            proves the theorem from the leaf lemmas (no new induction)
assemble.sh       concatenates spec + leaves + main, asks the kernel if the
                  result is axiom-free
leaves.json       manifest: id, file, difficulty, depends_on
```

## Why this makes work reliably completable

- **One leaf = one job.** A contributor proves a single lemma, not a 200-line
  development. Most leaves here are ★1–2 (a one-line `inversion`, an
  `induction … ; lia`).
- **Self-contained.** A leaf's prompt is `spec.v` + the lemma's dependencies
  (as statements) + the lemma to prove. The contributor's LLM has everything;
  it just fills the proof.
- **Binary, instant signal.** The kernel says yes/no — no "is this good enough?".
- **Difficulty-graded.** Pick a ★1 arithmetic leaf or the ★4 core (`outer_loop_bound`).
- **Independent & parallel.** Leaves depend on each other's *statements*, not
  proofs, so any order, any number of people.

## Certification = "small forces become a large one"

Run `assemble.sh`: it concatenates the shared spec, all leaves (dependency
order), and the assembly, then checks `Print Assumptions`. When it prints
**"Closed under the global context"**, every leaf has been discharged and the
theorem holds with **no assumptions** — built from many small proofs, none of
them trusted individually.

Progress is naturally visible as *"k / 10 leaves verified"*. If a leaf proves
too hard to one-shot (e.g. the ★4 `outer_loop_bound`), it splits further: its
internal `assert`s (`HBC`: `S i * i = i*(i-1) + 2*i`; `HBA`: `i+1 ≤ n → S i*i ≤
n*(n-1)`) are themselves trivial sub-leaves. Failures drive finer decomposition.

> In this example every leaf already carries a real proof, so `assemble.sh`
> certifies today. In production a leaf ships `Admitted` (status `open`) and a
> contributor replaces it; the verifier checks each leaf, and `assemble.sh`
> gates the final theorem.
