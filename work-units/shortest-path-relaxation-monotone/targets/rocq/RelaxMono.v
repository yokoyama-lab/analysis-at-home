(* analysis@home — work unit: shortest-path-relaxation-monotone (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Edge relaxation never increases a distance (monotone). *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint upd (p : list nat) (i v : nat) : list nat :=
  match p, i with [], _ => [] | _ :: t, 0 => v :: t | h :: t, S j => h :: upd t j v end.
Lemma upd_length : forall p i v, length (upd p i v) = length p.
Proof. induction p as [|h t IH]; intros i v; simpl. reflexivity.
  destruct i; simpl. reflexivity. rewrite IH. reflexivity. Qed.
Lemma nth_upd_eq : forall p i v d, i < length p -> nth i (upd p i v) d = v.
Proof. induction p as [|h t IH]; intros i v d Hi; simpl in *. lia.
  destruct i; simpl. reflexivity. apply IH. lia. Qed.
Lemma nth_upd_neq : forall p i j v d, i <> j -> nth j (upd p i v) d = nth j p d.
Proof. induction p as [|h t IH]; intros i j v d Hij; simpl. destruct i, j; reflexivity.
  destruct i, j; simpl; try reflexivity. lia. apply IH. lia. Qed.

(* Edge relaxation: dist[v] := min(dist[v], dist[u] + w). *)
Definition relax (d : list nat) (u v w : nat) : list nat :=
  upd d v (Nat.min (nth v d 0) (nth u d 0 + w)).
Theorem relaxation_monotone : forall d u v w i, nth i (relax d u v w) 0 <= nth i d 0.
Proof.
  intros d u v w i. unfold relax. destruct (Nat.eq_dec i v) as [->|Hne].
  - destruct (lt_dec v (length d)).
    + rewrite nth_upd_eq by exact l. apply Nat.le_min_l.
    + rewrite (nth_overflow (upd d v _)) by (rewrite upd_length; lia). lia.
  - rewrite nth_upd_neq by (intro; apply Hne; symmetry; exact H). lia.
Qed.
