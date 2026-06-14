(* analysis@home — work unit: sum-squares-of-odds (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 1^2 + 3^2 + ... + (2n-1)^2 = n(2n-1)(2n+1)/3. *)

Require Import Arith Lia.

Fixpoint sso (n:nat) := match n with 0=>0 | S m => sso m + ((2*m+1)*(2*m+1)) end.
Theorem sum_squares_of_odds : forall n, 3 * sso n + n = 4 * n * n * n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
