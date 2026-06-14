(* analysis@home — work unit: list-filter-tests (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). filter tests the predicate once per element. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint filterc (p : nat -> bool) (l : list nat) : list nat * nat :=
  match l with [] => ([], 0) | x :: xs => let '(r, c) := filterc p xs in ((if p x then x :: r else r), S c) end.
Theorem filter_tests : forall p l, snd (filterc p l) = length l.
Proof. intros p l. induction l as [|x xs IH].
  - reflexivity.
  - simpl. destruct (filterc p xs) as [r c] eqn:E. cbn [snd].
    try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
