(* analysis@home — work unit: dfs-soundness (Rocq target). VERIFIED (Print
   Assumptions: closed under the global context). DFS is sound: every vertex it
   visits is reachable (via the edge relation) from the initial frontier. *)

Require Import List Arith Lia.
Import ListNotations.
Fixpoint dfs (fuel : nat) (g : list (list nat)) (stack visited : list nat) : list nat :=
  match fuel with
  | 0 => visited
  | S f => match stack with
           | [] => visited
           | v :: rest =>
               if existsb (fun u => u =? v) visited
               then dfs f g rest visited
               else dfs f g (nth v g [] ++ rest) (v :: visited)
           end
  end.
Definition edge (g : list (list nat)) (u v : nat) : Prop := In v (nth u g []).
Inductive reach (g : list (list nat)) (src : list nat) : nat -> Prop :=
  | reach_init : forall v, In v src -> reach g src v
  | reach_step : forall u v, reach g src u -> edge g u v -> reach g src v.

(* Soundness: every vertex DFS visits is reachable from the initial frontier. *)
Theorem dfs_sound :
  forall fuel g src stack visited,
    (forall x, In x stack -> reach g src x) ->
    (forall x, In x visited -> reach g src x) ->
    forall x, In x (dfs fuel g stack visited) -> reach g src x.
Proof.
  induction fuel as [|f IH]; intros g src stack visited Hs Hv x Hx; simpl in Hx.
  - apply Hv; exact Hx.
  - destruct stack as [|v rest]. apply Hv; exact Hx.
    destruct (existsb (fun u => u =? v) visited) eqn:E.
    + apply (IH g src rest visited) with (x:=x).
      intros y Hy; apply Hs; right; exact Hy. exact Hv. exact Hx.
    + apply (IH g src (nth v g [] ++ rest) (v :: visited)) with (x:=x).
      * intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|Hy].
        apply (reach_step g src v y). apply Hs; left; reflexivity. unfold edge; exact Hy.
        apply Hs; right; exact Hy.
      * intros y [->|Hy]. apply Hs; left; reflexivity. apply Hv; exact Hy.
      * exact Hx.
Qed.
