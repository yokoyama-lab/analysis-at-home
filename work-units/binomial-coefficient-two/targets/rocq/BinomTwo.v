(* analysis@home — work unit: binomial-coefficient-two (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The binomial coefficient C(n,2) equals n(n-1)/2. *)

Require Import Arith Lia.

Fixpoint binom (n k:nat) := match n,k with _,0=>1 | 0,S _=>0 | S n',S k'=>binom n' k'+binom n' (S k') end.
Lemma binom_n0 : forall n, binom n 0 = 1. Proof. destruct n; reflexivity. Qed.
Lemma binom_one : forall n, binom n 1 = n.
Proof. induction n as [|m IH]; simpl. reflexivity. rewrite (binom_n0 m), IH. lia. Qed.
Theorem binom_two : forall n, 2 * binom n 2 + n = n * n.
Proof. induction n as [|m IH].
  - reflexivity.
  - change (binom (S m) 2) with (binom m 1 + binom m 2). rewrite binom_one. nia. Qed.
