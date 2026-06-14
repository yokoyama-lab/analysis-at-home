(* analysis@home — work unit: binomial-coefficient-succ-n (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The binomial coefficient C(n+1,n) equals n+1. *)

Require Import Arith Lia.

Fixpoint binom (n k:nat) := match n,k with _,0=>1 | 0,S _=>0 | S n',S k'=>binom n' k'+binom n' (S k') end.
Lemma binom_gt : forall n k, n < k -> binom n k = 0.
Proof. induction n as [|n' IH]; intros k Hk. destruct k. lia. reflexivity.
  destruct k as [|k']. lia. simpl. rewrite IH by lia. rewrite IH by lia. reflexivity. Qed.
Lemma binom_diag : forall n, binom n n = 1.
Proof. induction n as [|m IH]; simpl. reflexivity. rewrite IH. rewrite (binom_gt m (S m)) by lia. reflexivity. Qed.
Theorem binom_succ_n : forall n, binom (S n) n = S n.
Proof. induction n as [|m IH].
  - reflexivity.
  - change (binom (S (S m)) (S m)) with (binom (S m) m + binom (S m) (S m)).
    rewrite IH. rewrite (binom_diag (S m)). lia. Qed.
