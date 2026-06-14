(* analysis@home — work unit: list-append-operations (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Appending costs one cons per element of the first list. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint appendc (l1 l2 : list nat) : list nat * nat :=
  match l1 with [] => (l2, 0) | x :: xs => let '(r, c) := appendc xs l2 in (x :: r, S c) end.
Theorem append_operations : forall l1 l2, snd (appendc l1 l2) = length l1.
Proof. induction l1 as [|x xs IH]; intro l2.
  - reflexivity.
  - simpl. destruct (appendc xs l2) as [r c] eqn:E. cbn [snd].
    specialize (IH l2). try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
