(* analysis@home — work unit: sum-fourth-powers (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 1^4 + ... + n^4 = n(n+1)(2n+1)(3n^2+3n-1)/30. *)

Require Import Arith Lia.

Fixpoint s4 (n:nat) := match n with 0=>0 | S m => s4 m + (S m)*(S m)*(S m)*(S m) end.
Theorem sum_fourth_powers :
  forall n, 30 * s4 n + n*(n+1)*(2*n+1) = n*(n+1)*(2*n+1)*(3*n*n+3*n).
Proof. induction n as [|m IH]; simpl; nia. Qed.
