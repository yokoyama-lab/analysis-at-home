(* analysis@home — work unit: dfs-expansions-bound (Rocq target). VERIFIED (Print
   Assumptions: closed under the global context). A concrete fuel-based DFS provably
   marks each vertex at most once: its visited set stays distinct and bounded, so it
   performs at most |V| vertex expansions -- the V term of O(V+E) for a REAL algorithm. *)

Require Import List Arith Lia.
Import ListNotations.
Fixpoint dfs (fuel : nat) (g : list (list nat)) (stack visited : list nat) : list nat :=
  match fuel with
  | 0 => visited
  | S f =>
      match stack with
      | [] => visited
      | v :: rest =>
          if existsb (fun u => u =? v) visited
          then dfs f g rest visited
          else dfs f g (nth v g [] ++ rest) (v :: visited)
      end
  end.
Lemma existsb_false_not_In : forall v l, existsb (fun u => u =? v) l = false -> ~ In v l.
Proof. intros v l Hf Hin.
  assert (existsb (fun u => u =? v) l = true).
  { apply existsb_exists. exists v. split. exact Hin. apply Nat.eqb_refl. } congruence. Qed.
Lemma visited_vertex_bound : forall n l, NoDup l -> (forall x, In x l -> x < n) -> length l <= n.
Proof. intros n l Hnd Hb. rewrite <- (seq_length n 0). apply NoDup_incl_length. exact Hnd.
  intros x Hx. apply in_seq. split. lia. apply Hb. exact Hx. Qed.
Theorem dfs_visited_nodup : forall fuel g stack visited, NoDup visited -> NoDup (dfs fuel g stack visited).
Proof. induction fuel as [|f IH]; intros g stack visited Hnd; simpl. exact Hnd.
  destruct stack as [|v rest]. exact Hnd.
  destruct (existsb (fun u => u =? v) visited) eqn:E.
  - apply IH. exact Hnd.
  - apply IH. constructor. apply existsb_false_not_In. exact E. exact Hnd. Qed.
Lemma in_nth_bounded : forall (v n : nat) (g : list (list nat)) y,
  (forall adj, In adj g -> forall z, In z adj -> z < n) -> In y (nth v g []) -> y < n.
Proof. intros v n g y Hg Hy. destruct (lt_dec v (length g)).
  - apply (Hg (nth v g [])). apply nth_In. exact l. exact Hy.
  - rewrite nth_overflow in Hy by lia. simpl in Hy. contradiction. Qed.
Theorem dfs_visited_bounded :
  forall fuel g n stack visited,
    (forall adj, In adj g -> forall z, In z adj -> z < n) ->
    (forall x, In x stack -> x < n) ->
    (forall x, In x visited -> x < n) ->
    forall x, In x (dfs fuel g stack visited) -> x < n.
Proof.
  induction fuel as [|f IH]; intros g n stack visited Hg Hs Hv x Hx; simpl in Hx.
  - apply Hv. exact Hx.
  - destruct stack as [|v rest]. apply Hv; exact Hx.
    destruct (existsb (fun u => u =? v) visited) eqn:E.
    + apply (IH g n rest visited Hg) with (x:=x). intros y Hy. apply Hs. right; exact Hy. exact Hv. exact Hx.
    + apply (IH g n (nth v g [] ++ rest) (v :: visited) Hg) with (x:=x).
      * intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|Hy].
        apply (in_nth_bounded v n g y Hg Hy). apply Hs. right; exact Hy.
      * intros y [->|Hy]. apply Hs. left; reflexivity. apply Hv; exact Hy.
      * exact Hx.
Qed.
Theorem dfs_expansions_le_V :
  forall fuel g stack visited,
    NoDup visited ->
    (forall adj, In adj g -> forall z, In z adj -> z < length g) ->
    (forall x, In x stack -> x < length g) ->
    (forall x, In x visited -> x < length g) ->
    length (dfs fuel g stack visited) <= length g.
Proof.
  intros fuel g stack visited Hnd Hg Hs Hv. apply visited_vertex_bound.
  - apply dfs_visited_nodup. exact Hnd.
  - apply (dfs_visited_bounded fuel g (length g) stack visited); assumption.
Qed.
