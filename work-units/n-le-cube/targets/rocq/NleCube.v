(* analysis@home — work unit: n-le-cube (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Every n is at most its cube. *)

Require Import Arith Lia.

Theorem n_le_cube : forall n, n <= n * n * n.
Proof. intro n. destruct n as [|m]. lia. nia. Qed.
