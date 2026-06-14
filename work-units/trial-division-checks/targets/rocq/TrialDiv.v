(* analysis@home — work unit: trial-division-checks (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Testing divisibility of n by candidates down from k uses at most k checks (stops at the first divisor). *)

Require Import Arith Lia.

Fixpoint tdiv (n k : nat) : nat :=
  match k with 0 => 0 | S j => if (n mod (S j) =? 0) then 1 else S (tdiv n j) end.
Theorem trial_division_checks : forall n k, tdiv n k <= k.
Proof. intros n k. induction k as [|j IH].
  - simpl. lia.
  - cbn [tdiv]. destruct (n mod S j =? 0); lia. Qed.
