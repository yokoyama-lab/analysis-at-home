(* analysis@home — work unit: dfs-completeness (Rocq target). VERIFIED (Print
   Assumptions: closed under the global context). DFS is complete: if the worklist
   drains (enough fuel), it visits EVERY vertex reachable from the frontier. *)

Require Import List Arith Lia.
Import ListNotations.
(* DFS returning both the visited set and the leftover stack. *)
Fixpoint dfs2 (fuel : nat) (g : list (list nat)) (stack visited : list nat) : list nat * list nat :=
  match fuel with
  | 0 => (visited, stack)
  | S f => match stack with
           | [] => (visited, [])
           | v :: rest =>
               if existsb (fun u => u =? v) visited
               then dfs2 f g rest visited
               else dfs2 f g (nth v g [] ++ rest) (v :: visited)
           end
  end.
Definition edge (g : list (list nat)) (u v : nat) : Prop := In v (nth u g []).
Inductive reach (g : list (list nat)) (src : list nat) : nat -> Prop :=
  | reach_init : forall v, In v src -> reach g src v
  | reach_step : forall u v, reach g src u -> edge g u v -> reach g src v.

Lemma existsb_true_In : forall v l, existsb (fun u => u =? v) l = true -> In v l.
Proof. intros v l H. apply existsb_exists in H. destruct H as [x [Hx He]].
  apply Nat.eqb_eq in He. subst. exact Hx. Qed.

(* Closure invariant: every edge-target of a visited vertex is visited or pending. *)
Lemma dfs2_inv : forall fuel g stack visited,
  (forall u, In u visited -> forall w, edge g u w -> In w visited \/ In w stack) ->
  forall u, In u (fst (dfs2 fuel g stack visited)) -> forall w, edge g u w ->
    In w (fst (dfs2 fuel g stack visited)) \/ In w (snd (dfs2 fuel g stack visited)).
Proof.
  induction fuel as [|f IH]; intros g stack visited Hinv; simpl.
  - exact Hinv.
  - destruct stack as [|v rest].
    + intros u Hu w He. simpl. destruct (Hinv u Hu w He) as [H|H]. left; exact H. destruct H.
    + destruct (existsb (fun u => u =? v) visited) eqn:E.
      * apply IH. intros u Hu w He. destruct (Hinv u Hu w He) as [H|[->|H]].
        left; exact H. left; apply existsb_true_In; exact E. right; exact H.
      * apply IH. intros u [->|Hu] w He.
        right; apply in_or_app; left; exact He.
        destruct (Hinv u Hu w He) as [H|[->|H]].
        left; right; exact H. left; left; reflexivity. right; apply in_or_app; right; exact H.
Qed.

(* src stays in visited-or-stack. *)
Lemma dfs2_src : forall fuel g stack visited x,
  (In x visited \/ In x stack) ->
  In x (fst (dfs2 fuel g stack visited)) \/ In x (snd (dfs2 fuel g stack visited)).
Proof.
  induction fuel as [|f IH]; intros g stack visited x H; simpl.
  - exact H.
  - destruct stack as [|v rest].
    + destruct H as [H|H]. left; exact H. destruct H.
    + destruct (existsb (fun u => u =? v) visited) eqn:E.
      * apply IH. destruct H as [H|[->|H]]. left; exact H. left; apply existsb_true_In; exact E. right; exact H.
      * apply IH. destruct H as [H|[->|H]]. left; right; exact H. left; left; reflexivity.
        right; apply in_or_app; right; exact H.
Qed.

(* Completeness: if the stack drains (enough fuel), DFS visits every reachable vertex. *)
Theorem dfs_complete : forall fuel g src v,
  snd (dfs2 fuel g src []) = [] ->
  reach g src v ->
  In v (fst (dfs2 fuel g src [])).
Proof.
  intros fuel g src v Hterm Hr.
  assert (Hclo : forall u, In u (fst (dfs2 fuel g src [])) -> forall w, edge g u w -> In w (fst (dfs2 fuel g src []))).
  { intros u Hu w He. pose proof (dfs2_inv fuel g src [] ltac:(intros u0 H0; destruct H0) u Hu w He) as Hd.
    destruct Hd as [H|H]. exact H. rewrite Hterm in H. destruct H. }
  induction Hr as [v0 Hin | u w Hr0 IH He].
  - pose proof (dfs2_src fuel g src [] v0 (or_intror Hin)) as Hs.
    destruct Hs as [Hs|Hs]. exact Hs. rewrite Hterm in Hs. destruct Hs.
  - apply (Hclo u IH w). exact He.
Qed.
