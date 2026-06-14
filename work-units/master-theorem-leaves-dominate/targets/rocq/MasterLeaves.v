(* analysis@home — work unit: master-theorem-leaves-dominate (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). When leaves dominate (a=4>b^d=2), T(n)=4T(n/2)+n is Theta(n^2). *)

Require Import Arith Lia.

Theorem master_leaves_dominate :
  forall (T : nat -> nat), T 0 = 0 -> (forall k, T (S k) <= 4 * T k + 2 ^ (S k)) -> forall k, T k + 2 ^ k <= 4 ^ k.
Proof. intros T H0 Hrec. induction k as [|m IH].
  - rewrite H0. simpl. lia.
  - assert (E2 : 2 ^ (S m) = 2 * 2 ^ m) by reflexivity.
    assert (E4 : 4 ^ (S m) = 4 * 4 ^ m) by reflexivity. pose proof (Hrec m). nia. Qed.
