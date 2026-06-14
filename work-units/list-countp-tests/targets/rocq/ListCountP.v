(* analysis@home — work unit: list-countp-tests (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Counting elements satisfying a predicate uses n tests. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint countpc (p : nat -> bool) (l : list nat) : nat * nat :=
  match l with [] => (0, 0) | x :: xs => let '(k, c) := countpc p xs in ((if p x then S k else k), S c) end.
Theorem list_countp_tests : forall p l, snd (countpc p l) = length l.
Proof. intros p l. induction l as [|x xs IH].
  - reflexivity.
  - simpl. destruct (countpc p xs) as [k c] eqn:E. cbn [snd]. try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
