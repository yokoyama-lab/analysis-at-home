(* analysis@home — work unit: list-foldr-operations (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A right fold over a list of length n uses n applications. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint foldrc (f : nat -> nat -> nat) (b : nat) (l : list nat) : nat * nat :=
  match l with [] => (b, 0) | x :: xs => let '(r, c) := foldrc f b xs in (f x r, S c) end.
Theorem list_foldr_operations : forall f b l, snd (foldrc f b l) = length l.
Proof. intros f b l. induction l as [|x xs IH].
  - reflexivity.
  - simpl. destruct (foldrc f b xs) as [r c] eqn:E. cbn [snd].
    try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
