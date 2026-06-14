(* analysis@home — work unit: binary-counter-increments (Rocq target)
 *
 * Cost model: func-ops / counts = ["bit-flip"].  claim_kind: complexity (amortized).
 *
 * VERIFIED (no Admitted/Axiom; Print Assumptions: closed under the global
 * context). Performing n increments on a binary counter, starting from empty,
 * costs at most 2n bit flips — the classic AMORTIZED (aggregate) bound, proved
 * via the potential = popcount: total flips + ones(state) = 2n.
 * The lean/agda/isabelle targets remain open. *)

Require Import List Arith Lia.
Import ListNotations.

(* binary counter, least-significant bit first; true = 1 *)
Fixpoint count_ones (bs : list bool) : nat :=
  match bs with
  | [] => 0
  | true :: r => S (count_ones r)
  | false :: r => count_ones r
  end.

(* increment: returns the new counter and the number of bit flips it performed *)
Fixpoint incr (bs : list bool) : list bool * nat :=
  match bs with
  | [] => ([true], 1)
  | false :: r => (true :: r, 1)
  | true :: r => let (r', c) := incr r in (false :: r', S c)
  end.

(* n increments from the empty counter, accumulating total flips *)
Fixpoint incr_n (n : nat) : list bool * nat :=
  match n with
  | 0 => ([], 0)
  | S k => let (bs, tot) := incr_n k in
           let (bs', c) := incr bs in (bs', tot + c)
  end.

Definition flips (n : nat) : nat := snd (incr_n n).

(* one increment: flips + ones(after) = 2 + ones(before) *)
Lemma incr_flips : forall bs,
  snd (incr bs) + count_ones (fst (incr bs)) = 2 + count_ones bs.
Proof.
  induction bs as [|b r IH].
  - reflexivity.
  - destruct b.
    + simpl. destruct (incr r) as [r' c] eqn:E. simpl.
      try (rewrite E in IH). simpl in IH. lia.
    + simpl. lia.
Qed.

(* aggregate (potential = popcount): total flips + ones(state) = 2n *)
Lemma incr_n_invariant : forall n,
  snd (incr_n n) + count_ones (fst (incr_n n)) = 2 * n.
Proof.
  induction n as [|k IH].
  - reflexivity.
  - simpl. destruct (incr_n k) as [bs tot] eqn:E.
    destruct (incr bs) as [bs' c] eqn:E2. simpl.
    pose proof (incr_flips bs) as Hf. rewrite E2 in Hf. simpl in Hf.
    simpl in IH. lia.
Qed.

(* amortized: n increments of a binary counter cost at most 2n bit flips. *)
Theorem binary_counter_increments_amortized :
  forall n, flips n <= 2 * n.
Proof.
  intros n. unfold flips.
  pose proof (incr_n_invariant n) as H. lia.
Qed.
