(* analysis@home — work unit: rev-append-correct (Rocq target).
 *
 * The O(n) list reversal via an accumulator is correct: `rapp l acc` (reverse l
 * onto acc) satisfies rapp l acc = rev l ++ acc, hence the tail-recursive
 * `fast_rev l = rapp l [] = rev l`. (The naive `rev` is quadratic via ++; this is
 * the linear one.)
 *   fast_rev_correct : fast_rev l = rev l.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List.
Import ListNotations.

Fixpoint rapp (l acc : list nat) : list nat :=
  match l with [] => acc | x :: t => rapp t (x :: acc) end.
Definition fast_rev (l : list nat) : list nat := rapp l [].

Lemma rapp_spec : forall l acc, rapp l acc = rev l ++ acc.
Proof.
  induction l as [|x t IH]; intro acc; [reflexivity|].
  simpl. rewrite IH, <- app_assoc. reflexivity.
Qed.

Theorem fast_rev_correct : forall l, fast_rev l = rev l.
Proof.
  intro l. unfold fast_rev. rewrite rapp_spec, app_nil_r. reflexivity.
Qed.
