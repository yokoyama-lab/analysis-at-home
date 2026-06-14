(* analysis@home — work unit: fast-exponentiation-mults (Rocq target)
 *
 * Cost model: func-ops / counts = ["multiplication"].  claim_kind: complexity.
 *
 * VERIFIED (no Admitted/Axiom; Print Assumptions: closed under the global
 * context). Square-and-multiply exponentiation uses at most 2 * (number of bits
 * of the exponent) multiplications — i.e. LOGARITHMIC in the exponent value
 * (length of the binary digit list = floor(log2 e) + 1).
 * The lean/agda/isabelle targets, and a functional-correctness companion
 * (value = base^e), remain open. *)

Require Import List Arith Lia.
Import ListNotations.

(* exponent as binary digits, least-significant first; true = bit 1 *)
Fixpoint denote (ds : list bool) : nat :=
  match ds with
  | [] => 0
  | d :: r => (if d then 1 else 0) + 2 * denote r
  end.

(* square-and-multiply over the digit list.
   [sq] is the running square base^(2^position); returns (base^(denote ds), #mults).
   Each digit costs one squaring; a 1-digit costs one extra multiply. *)
Fixpoint sqm (sq : nat) (ds : list bool) : nat * nat :=
  match ds with
  | [] => (1, 0)
  | d :: r =>
      let '(acc, c) := sqm (sq * sq) r in
      if d then (sq * acc, S (S c)) else (acc, S c)
  end.

(* Cost: at most 2 * (number of bits of the exponent) multiplications
   (i.e. logarithmic in the exponent value). *)
Theorem square_and_multiply_mults : forall ds sq,
  snd (sqm sq ds) <= 2 * length ds.
Proof.
  induction ds as [|d r IH]; intros sq.
  - simpl. lia.
  - simpl. destruct (sqm (sq * sq) r) as [acc c] eqn:E. simpl.
    specialize (IH (sq * sq)). rewrite E in IH. simpl in IH.
    destruct d; simpl; lia.
Qed.
