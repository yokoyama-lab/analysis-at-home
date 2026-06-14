(* analysis@home — work unit: list-all-tests (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Checking a predicate over all elements uses at most n tests. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint allc (p : nat -> bool) (l : list nat) : bool * nat :=
  match l with [] => (true, 0) | x :: xs => if p x then let '(b, c) := allc p xs in (b, S c) else (false, 1) end.
Theorem list_all_tests : forall p l, snd (allc p l) <= length l.
Proof. intros p l. induction l as [|x xs IH].
  - simpl. lia.
  - simpl. destruct (p x).
    + destruct (allc p xs) as [b c] eqn:E. cbn [snd]. try (rewrite E in IH). cbn [snd] in IH. lia.
    + cbn [snd]. lia. Qed.
