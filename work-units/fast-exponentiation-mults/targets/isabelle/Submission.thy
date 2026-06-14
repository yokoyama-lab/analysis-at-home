(* analysis@home — work unit: fast-exponentiation-mults (Isabelle/HOL target).
   VERIFIED: `isabelle build` checks this theory with no sorry/oops. Same theorem
   as the Rocq/Lean targets: square-and-multiply uses <= 2*(bits of exponent)
   multiplications. *)

theory Submission
  imports Main
begin

fun denote :: "bool list \<Rightarrow> nat" where
  "denote [] = 0"
| "denote (d # r) = (if d then 1 else 0) + 2 * denote r"

fun sqm :: "nat \<Rightarrow> bool list \<Rightarrow> nat \<times> nat" where
  "sqm sq [] = (1, 0)"
| "sqm sq (d # r) =
     (case sqm (sq * sq) r of (acc, c) \<Rightarrow> if d then (sq * acc, c + 2) else (acc, c + 1))"

theorem square_and_multiply_mults: "snd (sqm sq ds) \<le> 2 * length ds"
proof (induction ds arbitrary: sq)
  case Nil
  show ?case by simp
next
  case (Cons d r)
  obtain acc c where hc: "sqm (sq * sq) r = (acc, c)" by (cases "sqm (sq * sq) r")
  have ih: "c \<le> 2 * length r" using Cons.IH[of "sq * sq"] hc by simp
  have e: "snd (sqm sq (d # r)) \<le> c + 2" using hc by (cases d) auto
  have len: "2 * length (d # r) = 2 * length r + 2" by simp
  show ?case using e ih len by linarith
qed

end
