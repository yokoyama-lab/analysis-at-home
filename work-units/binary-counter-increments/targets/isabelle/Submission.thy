(* analysis@home — work unit: binary-counter-increments (Isabelle/HOL target).
   VERIFIED: `isabelle build` checks this theory with no sorry/oops. Same theorem
   as the Rocq/Lean targets: n increments cost <= 2n bit flips (amortized). *)

theory Submission
  imports Main
begin

fun count_ones :: "bool list \<Rightarrow> nat" where
  "count_ones [] = 0"
| "count_ones (True # r) = count_ones r + 1"
| "count_ones (False # r) = count_ones r"

fun incr :: "bool list \<Rightarrow> bool list \<times> nat" where
  "incr [] = ([True], 1)"
| "incr (False # r) = (True # r, 1)"
| "incr (True # r) = (case incr r of (r', c) \<Rightarrow> (False # r', c + 1))"

fun incrN :: "nat \<Rightarrow> bool list \<times> nat" where
  "incrN 0 = ([], 0)"
| "incrN (Suc k) = (case incrN k of (bs, tot) \<Rightarrow> case incr bs of (bs', c) \<Rightarrow> (bs', tot + c))"

definition flips :: "nat \<Rightarrow> nat" where
  "flips n = snd (incrN n)"

lemma incr_flips: "snd (incr bs) + count_ones (fst (incr bs)) = 2 + count_ones bs"
  by (induction bs rule: incr.induct) (auto split: prod.splits)

lemma incrN_invariant: "snd (incrN n) + count_ones (fst (incrN n)) = 2 * n"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc k)
  then show ?case
    using incr_flips[of "fst (incrN k)"]
    by (auto split: prod.splits)
qed

theorem binary_counter_increments_amortized: "flips n \<le> 2 * n"
  using incrN_invariant[of n] by (simp add: flips_def)

end
