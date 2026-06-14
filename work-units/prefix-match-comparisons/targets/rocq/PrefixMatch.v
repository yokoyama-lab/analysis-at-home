(* analysis@home — work unit: prefix-match-comparisons (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Comparing a pattern against a text position uses at most |pattern| comparisons (stops at the first mismatch). *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint pmatch (p t : list nat) {struct p} : bool * nat :=
  match p, t with
  | [], _ => (true, 0)
  | _, [] => (false, 0)
  | x::ps, y::ts => if x =? y then let '(b,c) := pmatch ps ts in (b, S c) else (false, 1)
  end.
Theorem prefix_match_comparisons : forall p t, snd (pmatch p t) <= length p.
Proof. induction p as [|x ps IH]; intros [|y ts]; simpl.
  - lia. - lia. - lia.
  - destruct (x =? y).
    + destruct (pmatch ps ts) as [b c] eqn:E. cbn [snd]. specialize (IH ts).
      try (rewrite E in IH). cbn [snd] in IH. lia.
    + cbn [snd]. lia. Qed.
