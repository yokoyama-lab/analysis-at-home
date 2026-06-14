/- analysis@home — work unit: fast-exponentiation-mults (Lean 4 target)
   VERIFIED: `lean` accepts this and `#print axioms square_and_multiply_mults`
   reports no `sorryAx`. Same theorem as the Rocq target: square-and-multiply
   uses <= 2 * (number of bits of the exponent) multiplications. Lean core only. -/

def denote : List Bool → Nat
  | [] => 0
  | d :: r => (if d then 1 else 0) + 2 * denote r

def sqm (sq : Nat) : List Bool → Nat × Nat
  | [] => (1, 0)
  | d :: r => let p := sqm (sq * sq) r; if d then (sq * p.1, p.2 + 2) else (p.1, p.2 + 1)

theorem square_and_multiply_mults (ds : List Bool) (sq : Nat) :
    (sqm sq ds).2 ≤ 2 * ds.length := by
  induction ds generalizing sq with
  | nil => simp [sqm]
  | cons d r ih =>
    have h := ih (sq * sq)
    simp only [sqm, List.length_cons]
    cases d <;> simp <;> omega
