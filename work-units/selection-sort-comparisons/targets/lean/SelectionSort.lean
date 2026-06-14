/- analysis@home — work unit: selection-sort-comparisons (Lean 4 target)
   VERIFIED: `lean` accepts this and `#print axioms selection_sort_comparisons_exact`
   reports no `sorryAx`. Same exact theorem as the Rocq target:
   2 * comparisons l = l.length * (l.length - 1). Lean core only. -/

def select (x : Nat) : List Nat → Nat × List Nat × Nat
  | [] => (x, [], 0)
  | y :: ys =>
      let p := select (if y < x then y else x) ys
      (p.1, (if y < x then x else y) :: p.2.1, p.2.2 + 1)

def ssort : Nat → List Nat → List Nat × Nat
  | 0, _ => ([], 0)
  | _ + 1, [] => ([], 0)
  | f + 1, x :: xs =>
      let p := select x xs
      let q := ssort f p.2.1
      (p.1 :: q.1, p.2.2 + q.2)

def comparisons (l : List Nat) : Nat := (ssort l.length l).2

theorem select_count (l : List Nat) (x : Nat) : (select x l).2.2 = l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons y ys ih =>
    simp only [select, List.length_cons]
    have := ih (if y < x then y else x); omega

theorem select_len (l : List Nat) (x : Nat) : (select x l).2.1.length = l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons y ys ih =>
    simp only [select, List.length_cons]
    have := ih (if y < x then y else x); omega

theorem ssort_cost (f : Nat) (l : List Nat) (h : l.length ≤ f) :
    2 * (ssort f l).2 = l.length * (l.length - 1) := by
  induction f generalizing l with
  | zero => simp only [Nat.le_zero, List.length_eq_zero_iff] at h; subst h; rfl
  | succ f ih =>
    cases l with
    | nil => rfl
    | cons x xs =>
      simp only [ssort]
      have hc := select_count xs x
      have hl := select_len xs x
      have hrec := ih (select x xs).2.1 (by simp only [List.length_cons] at h; omega)
      rw [hl] at hrec
      rw [hc]
      simp only [List.length_cons, Nat.add_sub_cancel]
      cases hn : xs.length with
      | zero => rw [hn] at hrec; omega
      | succ k =>
        rw [hn] at hrec
        simp only [Nat.add_sub_cancel] at hrec
        have e : (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by
          rw [Nat.succ_mul, Nat.mul_succ]; omega
        rw [e]; omega

theorem selection_sort_comparisons_exact (l : List Nat) :
    2 * comparisons l = l.length * (l.length - 1) := by
  simpa [comparisons] using ssort_cost l.length l (Nat.le_refl _)
