<!-- Porting task for a contributor's own LLM (lean | agda | isabelle target).
The Rocq target is verified; mirror its cost model. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that the Tower of
Hanoi for n disks takes exactly 2^n − 1 moves.

Mirror the Rocq development
(`work-units/tower-of-hanoi-moves/targets/rocq/TowerOfHanoi.v`):
- `hanoi_moves 0 = 0`, `hanoi_moves (n+1) = 2*hanoi_moves n + 1`;
- prove the division-free `hanoi_moves n + 1 = 2 ^ n`.

Return only the proof-assistant source, with no axioms / sorry / admit /
postulate, so the kernel accepts it.
