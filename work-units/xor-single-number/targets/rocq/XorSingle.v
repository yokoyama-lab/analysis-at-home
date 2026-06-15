(* analysis@home — work unit: xor-single-number (Rocq target).
 *
 * The XOR "single number" trick: in a list where one value appears once and
 * every other value appears in pairs, a SINGLE left-to-right XOR fold recovers
 * the lone value — O(1) extra space, no sorting, no hashing. The surprise rests
 * on two facts about bitwise XOR: it is commutative/associative (so the fold is
 * order-independent — proved as Permutation invariance) and self-cancelling
 * (x XOR x = 0).
 *   single_number : Permutation l (m :: d ++ d) -> xorsum l = m.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith List Permutation.
Import ListNotations.

Definition xorsum (l : list nat) : nat := fold_right Nat.lxor 0 l.

Lemma xorsum_cons : forall a l, xorsum (a :: l) = Nat.lxor a (xorsum l).
Proof. reflexivity. Qed.

Lemma xorsum_app : forall l1 l2, xorsum (l1 ++ l2) = Nat.lxor (xorsum l1) (xorsum l2).
Proof.
  unfold xorsum. induction l1 as [|a l1 IH]; intro l2; simpl.
  - now rewrite Nat.lxor_0_l.
  - rewrite IH. now rewrite Nat.lxor_assoc.
Qed.

(* Order-independence: the fold value is invariant under permutation. *)
Lemma xorsum_perm : forall l1 l2, Permutation l1 l2 -> xorsum l1 = xorsum l2.
Proof.
  intros l1 l2 H. induction H.
  - reflexivity.
  - rewrite !xorsum_cons. now rewrite IHPermutation.
  - rewrite !xorsum_cons, <- !Nat.lxor_assoc. f_equal. apply Nat.lxor_comm.
  - transitivity (xorsum l'); assumption.
Qed.

(* Two copies of any list cancel to 0. *)
Lemma xorsum_dup : forall d, xorsum (d ++ d) = 0.
Proof. intro d. rewrite xorsum_app. apply Nat.lxor_nilpotent. Qed.

(* The single-number theorem: the lone element survives. *)
Theorem single_number : forall l m d,
  Permutation l (m :: d ++ d) -> xorsum l = m.
Proof.
  intros l m d H. rewrite (xorsum_perm _ _ H).
  rewrite xorsum_cons, xorsum_dup. apply Nat.lxor_0_r.
Qed.
