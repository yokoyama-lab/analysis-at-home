(* analysis@home — work unit: toposort-vertex-bound (Rocq target). VERIFIED (Print
   Assumptions: closed under the global context). A concrete Kahn-style topological
   sort processes each vertex at most once (output NoDup + bounded), so it emits at
   most |V| vertices -- the V term of its O(V+E) cost. *)

Require Import List Arith Lia.
Import ListNotations.

(* ===== Topological sort (Kahn) (Kahn): processes each vertex at most once ===== *)
Fixpoint kahn (fuel : nat) (g : list (list nat)) (ready output : list nat) : list nat :=
  match fuel with
  | 0 => output
  | S f => match ready with
           | [] => output
           | v :: rest =>
               if existsb (fun u => u =? v) output
               then kahn f g rest output
               else kahn f g (nth v g [] ++ rest) (v :: output)
           end
  end.
Lemma existsb_false_not_In : forall v l, existsb (fun u => u =? v) l = false -> ~ In v l.
Proof. intros v l Hf Hin. assert (existsb (fun u => u =? v) l = true).
  { apply existsb_exists. exists v. split. exact Hin. apply Nat.eqb_refl. } congruence. Qed.
Lemma visited_vertex_bound : forall n l, NoDup l -> (forall x, In x l -> x < n) -> length l <= n.
Proof. intros n l Hnd Hb. rewrite <- (seq_length n 0). apply NoDup_incl_length. exact Hnd.
  intros x Hx. apply in_seq. split. lia. apply Hb. exact Hx. Qed.
Lemma in_nth_bounded : forall (v n : nat) (g : list (list nat)) y,
  (forall adj, In adj g -> forall z, In z adj -> z < n) -> In y (nth v g []) -> y < n.
Proof. intros v n g y Hg Hy. destruct (lt_dec v (length g)).
  - apply (Hg (nth v g [])). apply nth_In. exact l. exact Hy.
  - rewrite nth_overflow in Hy by lia. simpl in Hy. contradiction. Qed.
Lemma kahn_nodup : forall fuel g ready output, NoDup output -> NoDup (kahn fuel g ready output).
Proof. induction fuel as [|f IH]; intros g ready output Hnd; simpl. exact Hnd.
  destruct ready as [|v rest]. exact Hnd.
  destruct (existsb (fun u => u =? v) output) eqn:E.
  - apply IH; exact Hnd.
  - apply IH. constructor. apply existsb_false_not_In; exact E. exact Hnd. Qed.
Lemma kahn_bounded : forall fuel g n ready output,
  (forall adj, In adj g -> forall z, In z adj -> z < n) ->
  (forall x, In x ready -> x < n) -> (forall x, In x output -> x < n) ->
  forall x, In x (kahn fuel g ready output) -> x < n.
Proof. induction fuel as [|f IH]; intros g n ready output Hg Hr Ho x Hx; simpl in Hx.
  - apply Ho; exact Hx.
  - destruct ready as [|v rest]. apply Ho; exact Hx.
    destruct (existsb (fun u => u =? v) output) eqn:E.
    + apply (IH g n rest output Hg) with (x:=x). intros y Hy. apply Hr; right; exact Hy. exact Ho. exact Hx.
    + apply (IH g n (nth v g [] ++ rest) (v :: output) Hg) with (x:=x).
      * intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|Hy].
        apply (in_nth_bounded v n g y Hg Hy). apply Hr; right; exact Hy.
      * intros y [->|Hy]. apply Hr; left; reflexivity. apply Ho; exact Hy.
      * exact Hx. Qed.
Theorem toposort_vertex_bound :
  forall fuel g ready output,
    NoDup output ->
    (forall adj, In adj g -> forall z, In z adj -> z < length g) ->
    (forall x, In x ready -> x < length g) ->
    (forall x, In x output -> x < length g) ->
    length (kahn fuel g ready output) <= length g.
Proof. intros fuel g ready output Hnd Hg Hr Ho. apply visited_vertex_bound.
  - apply kahn_nodup; exact Hnd.
  - apply (kahn_bounded fuel g (length g) ready output); assumption. Qed.
