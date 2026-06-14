(* analysis@home — work unit: even-or-odd (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Every natural number is either 2k or 2k+1. *)

Require Import Arith Lia.
Theorem even_or_odd : forall n, (exists k, n = 2 * k) \/ (exists k, n = 2 * k + 1).
Proof. induction n as [|m IH].
  - left. exists 0. reflexivity.
  - destruct IH as [[k Hk] | [k Hk]].
    + right. exists k. lia.
    + left. exists (S k). lia. Qed.
