(* analysis@home — work unit: centered-hexagonal-cube (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 1 + 7 + 19 + ... (centered hexagonals) sums to a perfect cube n^3. *)

Require Import Arith Lia.

Fixpoint sch (n:nat) := match n with 0=>0 | S m => sch m + (3*(S m)*m + 1) end.
Theorem centered_hexagonal_cube : forall n, sch n = n * n * n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
