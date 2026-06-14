(* analysis@home — work unit: geometric-sum-general (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). For base r>=2, the geometric sum obeys (r-1)*sum + 1 = r^n (generalizes the base-2/3/4/5 units). *)

Require Import Arith Lia.

Fixpoint gpow (b n:nat) := match n with 0=>0 | S m => gpow b m + b^m end.
Theorem geometric_sum_general : forall r n, gpow (S r) n * r + 1 = (S r) ^ n.
Proof. intros r n. induction n as [|m IH]; simpl. reflexivity. nia. Qed.
