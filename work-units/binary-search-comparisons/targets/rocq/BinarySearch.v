(* analysis@home — work unit: binary-search-comparisons (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Binary search: n < 2^k => at most k comparisons (= floor(lg n)+1). *)

Require Import Arith Lia.
Fixpoint bsearch (fuel n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f => match n with 0 => 0 | _ => S (bsearch f (n / 2)) end
  end.

Lemma half_lt : forall a b, a < 2 * b -> a / 2 < b.
Proof.
  intros a b H. pose proof (Nat.div_mod a 2 ltac:(lia)) as Hd.
  pose proof (Nat.mod_upper_bound a 2 ltac:(lia)) as Hm. lia.
Qed.

Theorem binary_search_comparisons :
  forall k fuel n, n < 2 ^ k -> bsearch fuel n <= k.
Proof.
  induction k as [|k' IHk]; intros fuel n Hn.
  - simpl in Hn. assert (n = 0) by lia. subst. destruct fuel; cbn [bsearch]; lia.
  - destruct fuel as [|f].
    + cbn [bsearch]. lia.
    + destruct n as [|n'].
      * cbn [bsearch]. lia.
      * cbn [bsearch].
        assert (E : 2 ^ S k' = 2 * 2 ^ k') by reflexivity.
        assert (Hhalf : S n' / 2 < 2 ^ k') by (apply half_lt; lia).
        specialize (IHk f (S n' / 2) Hhalf). lia.
Qed.
