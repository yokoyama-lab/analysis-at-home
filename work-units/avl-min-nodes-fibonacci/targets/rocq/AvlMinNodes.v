(* analysis@home — work unit: avl-min-nodes-fibonacci (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Min nodes of an AVL tree of height h is >= fib h (=> logarithmic height). *)

Require Import Arith Lia.

Fixpoint fib (n:nat) := match n with 0 => 0 | S m => match m with 0 => 1 | S k => fib m + fib k end end.
Fixpoint minnodes (h:nat) := match h with 0 => 1 | S h' => match h' with 0 => 2 | S h'' => 1 + minnodes h' + minnodes h'' end end.
Theorem avl_min_nodes : forall h, fib h <= minnodes h.
Proof.
  assert (H : forall h, fib h <= minnodes h /\ fib (S h) <= minnodes (S h)).
  { induction h as [|m [IH1 IH2]].
    - simpl. split; lia.
    - split.
      + exact IH2.
      + change (fib (S (S m))) with (fib (S m) + fib m).
        change (minnodes (S (S m))) with (1 + minnodes (S m) + minnodes m). lia. }
  intro h. apply H.
Qed.
