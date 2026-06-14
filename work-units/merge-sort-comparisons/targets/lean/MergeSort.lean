/- analysis@home — work unit: merge-sort-comparisons (Lean 4 target)
   VERIFIED: `lean` accepts this and `#print axioms merge_sort_comparisons_nlogn`
   reports no `sorryAx`. Same theorem as the Rocq target (O(n log n)):
   l.length ≤ 2^k → comparisons k l ≤ k * l.length. Lean core only (plain
   induction on the fuel / level; the nonlinear step is closed with omega plus
   manual distributivity). -/

def split : List Nat → List Nat × List Nat
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest => let p := split rest; (x :: p.1, y :: p.2)

def merge : Nat → List Nat → List Nat → List Nat × Nat
  | 0, l1, l2 => (l1 ++ l2, 0)
  | _ + 1, [], l2 => (l2, 0)
  | _ + 1, x :: xs, [] => (x :: xs, 0)
  | f + 1, x :: xs, y :: ys =>
      if x ≤ y then let p := merge f xs (y :: ys); (x :: p.1, p.2 + 1)
      else let p := merge f (x :: xs) ys; (y :: p.1, p.2 + 1)

def msort : Nat → List Nat → List Nat × Nat
  | 0, l => (l, 0)
  | _ + 1, [] => ([], 0)
  | _ + 1, [x] => ([x], 0)
  | k + 1, x :: y :: rest =>
      let s := split (x :: y :: rest)
      let p := msort k s.1
      let q := msort k s.2
      let m := merge (p.1.length + q.1.length) p.1 q.1
      (m.1, p.2 + q.2 + m.2)

def comparisons (k : Nat) (l : List Nat) : Nat := (msort k l).2

theorem split_total (l : List Nat) :
    (split l).1.length + (split l).2.length = l.length := by
  induction l using split.induct with
  | case1 => rfl
  | case2 x => rfl
  | case3 x y rest ih => simp only [split, List.length_cons]; omega

theorem split_bal (l : List Nat) :
    2 * (split l).1.length ≤ l.length + 1 ∧ 2 * (split l).2.length ≤ l.length := by
  induction l using split.induct with
  | case1 => simp [split]
  | case2 x => simp [split]
  | case3 x y rest ih => simp only [split, List.length_cons]; omega

theorem merge_length (f : Nat) : ∀ l1 l2,
    (merge f l1 l2).1.length = l1.length + l2.length := by
  induction f with
  | zero => intro l1 l2; simp [merge]
  | succ f ih =>
    intro l1 l2
    cases l1 with
    | nil => simp [merge]
    | cons x xs =>
      cases l2 with
      | nil => simp [merge]
      | cons y ys =>
        simp only [merge]
        split
        · simp only [List.length_cons]; rw [ih xs (y :: ys)]; simp only [List.length_cons]; omega
        · simp only [List.length_cons]; rw [ih (x :: xs) ys]; simp only [List.length_cons]; omega

theorem merge_cost (f : Nat) : ∀ l1 l2,
    (merge f l1 l2).2 ≤ l1.length + l2.length := by
  induction f with
  | zero => intro l1 l2; simp [merge]
  | succ f ih =>
    intro l1 l2
    cases l1 with
    | nil => simp [merge]
    | cons x xs =>
      cases l2 with
      | nil => simp [merge]
      | cons y ys =>
        simp only [merge]
        split
        · have := ih xs (y :: ys); simp only [List.length_cons] at this ⊢; omega
        · have := ih (x :: xs) ys; simp only [List.length_cons] at this ⊢; omega

theorem msort_length (k : Nat) : ∀ l, (msort k l).1.length = l.length := by
  induction k with
  | zero => intro l; rfl
  | succ k ih =>
    intro l
    cases l with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y rest =>
        simp only [msort]
        rw [merge_length, ih, ih]
        have := split_total (x :: y :: rest)
        omega

theorem msort_cost (k : Nat) : ∀ l, l.length ≤ 2 ^ k → comparisons k l ≤ k * l.length := by
  induction k with
  | zero => intro l _; simp [comparisons, msort]
  | succ k ih =>
    intro l h
    cases l with
    | nil => simp [comparisons, msort]
    | cons x xs =>
      cases xs with
      | nil => simp [comparisons, msort]
      | cons y rest =>
        rw [Nat.pow_succ] at h
        have htot := split_total (x :: y :: rest)
        have hbal := split_bal (x :: y :: rest)
        have h1 : (split (x :: y :: rest)).1.length ≤ 2 ^ k := by omega
        have h2 : (split (x :: y :: rest)).2.length ≤ 2 ^ k := by omega
        have Ic1 := ih (split (x :: y :: rest)).1 h1
        have Ic2 := ih (split (x :: y :: rest)).2 h2
        have hml1 := msort_length k (split (x :: y :: rest)).1
        have hml2 := msort_length k (split (x :: y :: rest)).2
        have Hcm := merge_cost ((msort k (split (x :: y :: rest)).1).1.length
                              + (msort k (split (x :: y :: rest)).2).1.length)
                              (msort k (split (x :: y :: rest)).1).1
                              (msort k (split (x :: y :: rest)).2).1
        simp only [comparisons, msort] at Ic1 Ic2 ⊢
        have dist : k * (split (x :: y :: rest)).1.length + k * (split (x :: y :: rest)).2.length
                  = k * (x :: y :: rest).length := by rw [← Nat.mul_add, htot]
        have succm : (k + 1) * (x :: y :: rest).length
                  = k * (x :: y :: rest).length + (x :: y :: rest).length := by rw [Nat.succ_mul]
        omega

theorem merge_sort_comparisons_nlogn (k : Nat) (l : List Nat) (h : l.length ≤ 2 ^ k) :
    comparisons k l ≤ k * l.length := msort_cost k l h

-- contributor: trivial re-check
