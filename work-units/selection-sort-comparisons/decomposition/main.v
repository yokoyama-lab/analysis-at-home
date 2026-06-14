(* assembly: the exact count from the cost leaf. *)
Theorem selection_sort_comparisons_exact : forall l,
  2 * comparisons l = length l * (length l - 1).
Proof.
  intros l. unfold comparisons. apply ssort_cost. lia.
Qed.
