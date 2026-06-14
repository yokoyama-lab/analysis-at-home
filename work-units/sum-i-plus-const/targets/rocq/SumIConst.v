(* analysis@home — work unit: sum-i-plus-const (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Sum of (i+c) over i=1..n = n(n+1)/2 + cn. *)

Require Import Arith Lia.

Fixpoint sic (c n:nat) := match n with 0 => 0 | S m => sic c m + (S m + c) end.
Theorem sum_i_plus_const : forall c n, 2 * sic c n = n * (n + 1) + 2 * c * n.
Proof. intros c n. induction n as [|m IH]; simpl; nia. Qed.
