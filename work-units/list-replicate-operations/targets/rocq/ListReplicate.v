(* analysis@home — work unit: list-replicate-operations (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Building a list of n copies uses exactly n cons operations. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint replicatec (n x : nat) : list nat * nat :=
  match n with 0 => ([], 0) | S m => let '(r, c) := replicatec m x in (x :: r, S c) end.
Theorem list_replicate_operations : forall n x, snd (replicatec n x) = n.
Proof. intros n x. induction n as [|m IH].
  - reflexivity.
  - simpl. destruct (replicatec m x) as [r c] eqn:E. cbn [snd]. try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
