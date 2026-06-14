(* analysis@home — work unit: sum-multiples-of-k (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). k + 2k + ... + nk = k*n(n+1)/2. *)

Require Import Arith Lia.

Fixpoint smk (k n:nat) := match n with 0=>0 | S m => smk k m + k*(S m) end.
Theorem sum_multiples_of_k : forall k n, 2 * smk k n = k * (n * (n+1)).
Proof. intros k n. induction n as [|m IH]; simpl; nia. Qed.
