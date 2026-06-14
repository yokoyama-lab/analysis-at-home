(* analysis@home — work unit: sum-of-triangulars (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The sum of the first n triangular numbers equals n(n+1)(n+2)/6 (tetrahedral). *)

Require Import Arith Lia.

Fixpoint tri (n : nat) : nat := match n with 0 => 0 | S m => tri m + S m end.
Fixpoint sumtri (n : nat) : nat := match n with 0 => 0 | S m => sumtri m + tri (S m) end.
Theorem sum_triangulars : forall n, 6 * sumtri n = n * (n + 1) * (n + 2).
Proof. assert (T : forall n, 2 * tri n = n * (n+1)) by (induction n; simpl; nia).
  induction n as [|m IH]; simpl. reflexivity. pose proof (T (S m)). simpl in *. nia. Qed.
