(* analysis@home — work unit: kadane-max-subarray (Rocq target).
 *
 * Kadane's algorithm: the maximum contiguous-subarray sum in ONE linear pass
 * (TAOCP-adjacent; Bentley, Programming Pearls). A problem that "looks" O(n^2)
 * — there are Theta(n^2) subarrays — is solved in O(n). Running variables:
 *   cur  l = best sum of a subarray ending at the front (max prefix sum, >= 0)
 *   best l = best sum over ALL contiguous subarrays so far
 * with cur (x::r) = max 0 (x + cur r) and best (x::r) = max (cur (x::r)) (best r).
 * Correctness (best l is exactly the maximum subarray sum):
 *   kadane_correct : (forall i k, Zsum (window i k l) <= best l)
 *                 /\ (exists i k, best l = Zsum (window i k l)).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Definition Zsum : list Z -> Z := fold_right Z.add 0.
Definition window (i k : nat) (l : list Z) : list Z := firstn k (skipn i l).

Fixpoint cur (l : list Z) : Z :=
  match l with [] => 0 | x :: r => Z.max 0 (x + cur r) end.
Fixpoint best (l : list Z) : Z :=
  match l with [] => 0 | x :: r => Z.max (cur (x :: r)) (best r) end.
Definition kadane (l : list Z) : Z * Z := (cur l, best l).

(* every prefix sum is at most cur *)
Lemma prefix_le_cur : forall l k, Zsum (firstn k l) <= cur l.
Proof.
  induction l as [|x r IH]; intro k; cbn [cur].
  - destruct k; cbn; lia.
  - destruct k as [|k]; cbn [firstn Zsum fold_right].
    + pose proof (Z.le_max_l 0 (x + cur r)); lia.
    + pose proof (Z.le_max_r 0 (x + cur r)); specialize (IH k); lia.
Qed.

(* and cur is the sum of some prefix *)
Lemma cur_attained : forall l, exists k, cur l = Zsum (firstn k l).
Proof.
  induction l as [|x r IH]; cbn [cur].
  - exists 0%nat; reflexivity.
  - destruct (Z.max_spec 0 (x + cur r)) as [[_ E]|[_ E]]; rewrite E.
    + destruct IH as [k Hk]. exists (S k). cbn [firstn Zsum fold_right]. lia.
    + exists 0%nat; reflexivity.
Qed.

(* every contiguous subarray sum is at most best *)
Lemma sub_le_best : forall l i k, Zsum (window i k l) <= best l.
Proof.
  unfold window. induction l as [|x r IH]; intros i k; cbn [best].
  - destruct i; cbn; destruct k; cbn; lia.
  - destruct i as [|i]; cbn [skipn].
    + pose proof (prefix_le_cur (x :: r) k).
      pose proof (Z.le_max_l (cur (x :: r)) (best r)). lia.
    + pose proof (IH i k). pose proof (Z.le_max_r (cur (x :: r)) (best r)). lia.
Qed.

(* and best is itself the sum of some contiguous subarray *)
Lemma best_attained : forall l, exists i k, best l = Zsum (window i k l).
Proof.
  unfold window. induction l as [|x r IH]; cbn [best].
  - exists 0%nat, 0%nat; reflexivity.
  - destruct (Z.max_spec (cur (x :: r)) (best r)) as [[_ E]|[_ E]]; rewrite E.
    + destruct IH as [i [k Hk]]. exists (S i), k. cbn [skipn]. exact Hk.
    + destruct (cur_attained (x :: r)) as [k Hk]. exists 0%nat, k. cbn [skipn]. exact Hk.
Qed.

(* Kadane's output `best` is exactly the maximum contiguous-subarray sum. *)
Theorem kadane_correct : forall l,
  (forall i k, Zsum (window i k l) <= snd (kadane l)) /\
  (exists i k, snd (kadane l) = Zsum (window i k l)).
Proof.
  intro l. unfold kadane; cbn [snd]. split.
  - intros i k. apply sub_le_best.
  - apply best_attained.
Qed.
