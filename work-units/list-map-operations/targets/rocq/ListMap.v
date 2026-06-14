(* analysis@home — work unit: list-map-operations (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). map applies the function once per element. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint mapc (f : nat -> nat) (l : list nat) : list nat * nat :=
  match l with [] => ([], 0) | x :: xs => let '(r, c) := mapc f xs in (f x :: r, S c) end.
Theorem map_operations : forall f l, snd (mapc f l) = length l.
Proof. intros f l. induction l as [|x xs IH].
  - reflexivity.
  - simpl. destruct (mapc f xs) as [r c] eqn:E. cbn [snd].
    try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
