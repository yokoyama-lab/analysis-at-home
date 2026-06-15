import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

def lr_changes (cur : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs =>
      if cur < x then
        Nat.succ (lr_changes x xs)
      else
        lr_changes cur xs

theorem algorithm_m_changes_le : ∀ (l : List Nat) (cur : Nat),
    lr_changes cur l ≤ l.length := by
  intro l
  induction l with
  | nil =>
      intro cur
      simp [lr_changes]
  | cons x xs ih =>
      intro cur
      simp [lr_changes]
      split
      · have h := ih x
        omega
      · exact ih cur
