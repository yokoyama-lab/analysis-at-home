(* analysis@home — work unit: list-any-tests (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Checking whether any element satisfies a predicate uses at most n tests. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint anyc (p : nat -> bool) (l : list nat) : bool * nat :=
  match l with [] => (false, 0) | x :: xs => if p x then (true, 1) else let '(b, c) := anyc p xs in (b, S c) end.
Theorem list_any_tests : forall p l, snd (anyc p l) <= length l.
Proof. intros p l. induction l as [|x xs IH].
  - simpl. lia.
  - simpl. destruct (p x).
    + cbn [snd]. lia.
    + destruct (anyc p xs) as [b c] eqn:E. cbn [snd]. try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
