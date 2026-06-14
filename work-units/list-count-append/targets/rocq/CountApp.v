(* analysis@home — work unit: list-count-append (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The number of occurrences of x in l1 ++ l2 is the sum of the counts. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint occ (x : nat) (l : list nat) := match l with [] => 0 | y :: ys => (if y =? x then 1 else 0) + occ x ys end.
Theorem list_count_append : forall x l1 l2, occ x (l1 ++ l2) = occ x l1 + occ x l2.
Proof. intros x l1 l2. induction l1 as [|y ys IH]; simpl. reflexivity. rewrite IH. lia. Qed.
