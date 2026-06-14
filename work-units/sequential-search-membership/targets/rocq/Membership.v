(* analysis@home — work unit: sequential-search-membership (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Membership search uses at most n comparisons. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint memberc (x : nat) (l : list nat) : bool * nat :=
  match l with [] => (false, 0) | y :: ys => if x =? y then (true, 1) else let '(b, c) := memberc x ys in (b, S c) end.
Theorem membership_comparisons : forall x l, snd (memberc x l) <= length l.
Proof. intros x l. induction l as [|y ys IH].
  - simpl. lia.
  - simpl. destruct (x =? y).
    + cbn [snd]. lia.
    + destruct (memberc x ys) as [b c] eqn:E. cbn [snd].
      try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
