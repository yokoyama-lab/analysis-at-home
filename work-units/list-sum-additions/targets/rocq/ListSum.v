(* analysis@home — work unit: list-sum-additions (Rocq target)
 *
 * Cost model: func-ops / counts = ["addition"].  claim_kind: complexity.
 *
 * A fundamental fact (TAOCP Vol. 1/2, basic operation counts): adding the n
 * numbers in a list takes exactly n-1 additions. The instrumented summation
 * folds the tail into an accumulator seeded with the head, counting one addition
 * per folded element; hence the head costs nothing and the count is n-1.
 *
 *   list_sum_additions : snd (sum_list l) = pred (length l).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint sumc (acc : nat) (l : list nat) : nat * nat :=
  match l with
  | [] => (acc, 0)
  | x :: xs => let '(s, c) := sumc (acc + x) xs in (s, S c)
  end.

Definition sum_list (l : list nat) : nat * nat :=
  match l with [] => (0, 0) | x :: xs => sumc x xs end.

Lemma sumc_count : forall l acc, snd (sumc acc l) = length l.
Proof.
  induction l as [|x xs IH]; intro acc.
  - reflexivity.
  - simpl. destruct (sumc (acc + x) xs) as [s c] eqn:E. cbn [snd].
    specialize (IH (acc + x)). rewrite E in IH. cbn [snd] in IH. lia.
Qed.

Theorem list_sum_additions : forall l, snd (sum_list l) = pred (length l).
Proof.
  intros [|x xs].
  - reflexivity.
  - simpl. rewrite sumc_count. reflexivity.
Qed.
