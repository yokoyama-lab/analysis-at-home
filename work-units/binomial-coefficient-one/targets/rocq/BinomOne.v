(* analysis@home — work unit: binomial-coefficient-one (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The binomial coefficient C(n,1) equals n. *)

Require Import Arith Lia.

Fixpoint binom (n k : nat) : nat :=
  match n, k with | _, 0 => 1 | 0, S _ => 0 | S n', S k' => binom n' k' + binom n' (S k') end.
Lemma binom_n0 : forall n, binom n 0 = 1.
Proof. destruct n; reflexivity. Qed.
Theorem binom_one : forall n, binom n 1 = n.
Proof. induction n as [|m IH]; simpl. reflexivity. rewrite (binom_n0 m), IH. lia. Qed.
