(* assembly: the amortized bound from the invariant leaf. *)
Theorem binary_counter_increments_amortized : forall n, flips n <= 2 * n.
Proof.
  intros n. unfold flips.
  pose proof (incr_n_invariant n) as H. lia.
Qed.
