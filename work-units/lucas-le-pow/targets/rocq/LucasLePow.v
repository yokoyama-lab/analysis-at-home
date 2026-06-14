(* analysis@home — work unit: lucas-le-pow (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The n-th Lucas number is at most 2^(n+1). *)

Require Import Arith Lia.

Fixpoint lucas (n:nat) := match n with 0 => 2 | S m => match m with 0 => 1 | S k => lucas m + lucas k end end.
Theorem lucas_le_pow : forall n, lucas n <= 2 ^ (S n).
Proof.
  assert (H : forall n, lucas n <= 2^(S n) /\ lucas (S n) <= 2^(S (S n))).
  { induction n as [|m [IH1 IH2]].
    - simpl. split; lia.
    - split. exact IH2.
      change (lucas (S (S m))) with (lucas (S m) + lucas m).
      assert (2 ^ (S (S (S m))) = 2 * 2 ^ (S (S m))) by reflexivity.
      assert (2 ^ (S (S m)) = 2 * 2 ^ (S m)) by reflexivity. lia. }
  intro n. apply H.
Qed.
