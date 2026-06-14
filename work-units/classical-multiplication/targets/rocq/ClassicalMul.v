(* analysis@home — work unit: classical-multiplication (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Multiplying an n-digit by an m-digit number uses n*m digit products. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint mulrow (b : list nat) : nat := match b with [] => 0 | _::ys => S (mulrow ys) end.
Fixpoint mulc (a b : list nat) : nat := match a with [] => 0 | _::xs => mulrow b + mulc xs b end.
Lemma mulrow_len : forall b, mulrow b = length b.
Proof. induction b; simpl; [reflexivity | rewrite IHb; reflexivity]. Qed.
Theorem classical_multiplication_products : forall a b, mulc a b = length a * length b.
Proof. induction a as [|x xs IH]; intro b; simpl. reflexivity. rewrite mulrow_len, IH. lia. Qed.
