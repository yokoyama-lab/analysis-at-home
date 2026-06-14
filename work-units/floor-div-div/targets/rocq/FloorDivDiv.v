(* analysis@home — work unit: floor-div-div (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Dividing by a then by b equals dividing by a*b (floor division). *)

Require Import Arith Lia.

Theorem floor_div_div : forall n a b, a <> 0 -> b <> 0 -> (n / a) / b = n / (a * b).
Proof. intros n a b Ha Hb. apply Nat.div_div; lia. Qed.
