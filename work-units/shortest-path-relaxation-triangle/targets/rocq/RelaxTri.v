(* analysis@home — work unit: shortest-path-relaxation-triangle (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). After relaxing (u,v,w), dist[v] <= dist[u]+w. *)

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
Theorem relaxation_triangle : forall d u v w, v < length d -> nth v (relax d u v w) 0 <= nth u d 0 + w.
Proof.
  intros d u v w Hv. unfold relax. rewrite nth_upd_eq by exact Hv. apply Nat.le_min_r.
Qed.
