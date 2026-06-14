(* analysis@home — work unit: quicksort-average-comparisons (Isabelle/HOL target).
   VERIFIED: `isabelle build` checks this theory with no incompleteness markers.
   Same theorem as the Rocq target (QuicksortAverage.v): the solution Cq of the
   reduced quicksort-average recurrence equals the closed form
   Cf n = 2(n+1)*harm n - 4*n, where harm n is the n-th harmonic number. Worked
   over the rationals (rat); the inductive step (the closed form solves the
   recurrence) is discharged by field_simps. *)

theory Submission
  imports Complex_Main
begin

fun harm :: "nat \<Rightarrow> rat" where
  "harm 0 = 0"
| "harm (Suc m) = harm m + 1 / of_nat (Suc m)"

fun Cq :: "nat \<Rightarrow> rat" where
  "Cq 0 = 0"
| "Cq (Suc m) = (of_nat (Suc (Suc m)) * Cq m + 2 * of_nat m) / of_nat (Suc m)"

definition Cf :: "nat \<Rightarrow> rat" where
  "Cf n = 2 * of_nat (Suc n) * harm n - 4 * of_nat n"

theorem quicksort_average_closed_form: "Cq n = Cf n"
proof (induction n)
  case 0
  show ?case by (simp add: Cf_def)
next
  case (Suc m)
  have nz: "(of_nat (Suc m)::rat) \<noteq> 0" by simp
  have "Cq (Suc m) = (of_nat (Suc (Suc m)) * Cf m + 2 * of_nat m) / of_nat (Suc m)"
    by (simp add: Suc.IH)
  also have "\<dots> = Cf (Suc m)"
    using nz by (simp add: Cf_def field_simps)
  finally show ?case .
qed

end
