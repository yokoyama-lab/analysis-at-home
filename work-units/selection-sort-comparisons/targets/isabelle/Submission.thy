(* analysis@home — work unit: selection-sort-comparisons (Isabelle/HOL target).
   VERIFIED: `isabelle build` checks this theory with no sorry/oops. Same exact
   theorem as the Rocq/Lean targets: 2*comparisons = n*(n-1). *)

theory Submission
  imports Main
begin

fun sel :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<times> nat list \<times> nat" where
  "sel x [] = (x, [], 0)"
| "sel x (y # ys) =
     (case sel (if y < x then y else x) ys of (m, rest, c) \<Rightarrow>
        (m, (if y < x then x else y) # rest, Suc c))"

fun ssort :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<times> nat" where
  "ssort 0 _ = ([], 0)"
| "ssort (Suc f) [] = ([], 0)"
| "ssort (Suc f) (x # xs) =
     (case sel x xs of (m, rest, c1) \<Rightarrow>
        case ssort f rest of (srt, c2) \<Rightarrow> (m # srt, c1 + c2))"

definition comparisons :: "nat list \<Rightarrow> nat" where
  "comparisons l = snd (ssort (length l) l)"

lemma sel_count: "snd (snd (sel x l)) = length l"
proof (induction l arbitrary: x)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  obtain m rest c where h: "sel (if y < x then y else x) ys = (m, rest, c)"
    by (cases "sel (if y < x then y else x) ys") auto
  show ?case using h Cons.IH[of "if y < x then y else x"] by simp
qed

lemma sel_len: "length (fst (snd (sel x l))) = length l"
proof (induction l arbitrary: x)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  obtain m rest c where h: "sel (if y < x then y else x) ys = (m, rest, c)"
    by (cases "sel (if y < x then y else x) ys") auto
  show ?case using h Cons.IH[of "if y < x then y else x"] by simp
qed

lemma ssort_cost: "length l \<le> f \<Longrightarrow> 2 * snd (ssort f l) = length l * (length l - 1)"
proof (induction f arbitrary: l)
  case 0 then show ?case by simp
next
  case (Suc f)
  show ?case
  proof (cases l)
    case Nil then show ?thesis by simp
  next
    case (Cons x xs)
    obtain m rest c1 where hs: "sel x xs = (m, rest, c1)" by (cases "sel x xs") auto
    obtain srt c2 where ht: "ssort f rest = (srt, c2)" by (cases "ssort f rest") auto
    have hc1: "c1 = length xs" using sel_count[of x xs] hs by simp
    have hlr: "length rest = length xs" using sel_len[of x xs] hs by simp
    have hf: "length rest \<le> f" using Suc.prems hlr Cons by simp
    have hc2: "2 * c2 = length xs * (length xs - 1)" using Suc.IH[OF hf] ht hlr by simp
    have hsnd: "snd (ssort (Suc f) (x # xs)) = c1 + c2" using hs ht by simp
    show ?thesis using hsnd hc1 hc2 Cons by (cases "length xs") (simp_all add: algebra_simps)
  qed
qed

theorem selection_sort_comparisons_exact:
  "2 * comparisons l = length l * (length l - 1)"
  using ssort_cost[of l "length l"] by (simp add: comparisons_def)

end
