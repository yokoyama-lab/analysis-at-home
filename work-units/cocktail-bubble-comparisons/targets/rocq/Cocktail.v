(* analysis@home — work unit: cocktail-bubble-comparisons (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Cocktail-shaker sort, like bubble sort, makes n(n-1)/2 comparisons in the worst case. *)

Require Import Arith Lia.

Fixpoint cbc (n:nat) := match n with 0 => 0 | S m => cbc m + m end.
Theorem cocktail_bubble_comparisons : forall n, 2 * cbc n + n = n * n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
