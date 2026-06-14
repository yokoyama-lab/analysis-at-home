(* analysis@home — work unit: list-product-mults (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Multiplying the n numbers in a list uses n-1 multiplications. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint prodc (acc : nat) (l : list nat) : nat * nat :=
  match l with [] => (acc, 0) | x :: xs => let '(p, c) := prodc (acc * x) xs in (p, S c) end.
Definition prod_list (l : list nat) := match l with [] => (1, 0) | x :: xs => prodc x xs end.
Lemma prodc_count : forall l acc, snd (prodc acc l) = length l.
Proof. induction l as [|x xs IH]; intro acc.
  - reflexivity.
  - simpl. destruct (prodc (acc*x) xs) as [p c] eqn:E. cbn [snd]. specialize (IH (acc*x)).
    try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
Theorem list_product_mults : forall l, snd (prod_list l) = pred (length l).
Proof. intros [|x xs]; [reflexivity | simpl; apply prodc_count]. Qed.
