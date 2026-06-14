/- analysis@home — work unit: binary-counter-increments (Lean 4 target)

   VERIFIED: `lean` accepts this file and
   `#print axioms binary_counter_increments_amortized` reports only the standard
   foundational axioms (propext, Quot.sound) — no `sorryAx`. Same theorem as the
   Rocq target: n increments cost at most 2n bit flips (amortized), via the
   potential = popcount invariant. Uses only Lean core (no Mathlib). -/

def countOnes : List Bool → Nat
  | [] => 0
  | true :: r => countOnes r + 1
  | false :: r => countOnes r

def incr : List Bool → List Bool × Nat
  | [] => ([true], 1)
  | false :: r => (true :: r, 1)
  | true :: r => let p := incr r; (false :: p.1, p.2 + 1)

def incrN : Nat → List Bool × Nat
  | 0 => ([], 0)
  | k + 1 => let p := incrN k; let q := incr p.1; (q.1, p.2 + q.2)

def flips (n : Nat) : Nat := (incrN n).2

theorem incr_flips (bs : List Bool) :
    (incr bs).2 + countOnes (incr bs).1 = 2 + countOnes bs := by
  induction bs with
  | nil => rfl
  | cons b r ih =>
    cases b <;> simp only [incr, countOnes] <;> omega

theorem incrN_invariant (n : Nat) :
    (incrN n).2 + countOnes (incrN n).1 = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [incrN]
    have h := incr_flips (incrN k).1
    omega

theorem binary_counter_increments_amortized (n : Nat) : flips n ≤ 2 * n := by
  have h := incrN_invariant n
  simp only [flips]
  omega
