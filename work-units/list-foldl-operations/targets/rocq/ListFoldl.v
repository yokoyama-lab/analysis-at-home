(* analysis@home — work unit: list-foldl-operations (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A left fold over a list of length n uses n applications. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint foldlc (f : nat -> nat -> nat) (acc : nat) (l : list nat) : nat * nat :=
  match l with [] => (acc, 0) | x :: xs => let '(r, c) := foldlc f (f acc x) xs in (r, S c) end.
Theorem list_foldl_operations : forall f l acc, snd (foldlc f acc l) = length l.
Proof. intros f l. induction l as [|x xs IH]; intro acc.
  - reflexivity.
  - simpl. destruct (foldlc f (f acc x) xs) as [r c] eqn:E. cbn [snd]. specialize (IH (f acc x)).
    try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
