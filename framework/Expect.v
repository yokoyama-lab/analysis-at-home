(* analysis@home — linearity of expectation (the compositional core).
 *
 * This is what makes average-case cost COMPOSITIONAL rather than ad hoc, and lets
 * us reach expectations over EXPONENTIAL outcome spaces (n! permutations, n^n
 * hash assignments) without enumerating them: a cost that is a sum of simpler
 * components (typically indicators) has expectation equal to the sum of their
 * expectations.
 *
 *   E f l : Q          the expected value of nat-valued `f` over the uniform
 *                      distribution on the finite outcome list `l`.
 *   E_add              E[f + g] = E[f] + E[g]                 (linearity)
 *   E_const            E[const c] = c
 *   E_linear_sum       E[Σ_{j∈js} comp_j] = Σ_{j∈js} E[comp_j]
 *
 * With E_linear_sum, the textbook moves — E[#records] = Σ_i P(i is a record),
 * E[#collisions] = Σ_{i<j} P(i,j collide) — become kernel-checked once each
 * per-component expectation (a marginal probability) is supplied. That is the
 * next step toward the deep average-case results.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List Arith Lia QArith ZArith.
Import ListNotations.

Fixpoint list_sum (l : list nat) : nat :=
  match l with [] => 0 | x :: t => x + list_sum t end.

Open Scope Q_scope.

(* expected value of nat-valued `f` over the uniform distribution on `l` *)
Definition E {A} (f : A -> nat) (l : list A) : Q :=
  inject_Z (Z.of_nat (list_sum (map f l))) / inject_Z (Z.of_nat (length l)).

(* sum of a list of rationals (the RHS of finite-family linearity) *)
Fixpoint qsumQ (l : list Q) : Q := match l with [] => 0 | x :: t => x + qsumQ t end.

Lemma q_div_add : forall a b c, (a + b) / c == a / c + b / c.
Proof. intros a b c. unfold Qdiv. ring. Qed.

Lemma list_sum_map_add : forall A (f g : A -> nat) l,
  (list_sum (map (fun a => f a + g a) l) = list_sum (map f l) + list_sum (map g l))%nat.
Proof. intros A f g l. induction l as [|x t IH]; cbn [map list_sum]; lia. Qed.

Lemma list_sum_map_const : forall A c (l : list A),
  (list_sum (map (fun _ => c) l) = c * length l)%nat.
Proof. intros A c l. induction l as [|x t IH]; cbn [map list_sum length]; lia. Qed.

Lemma inj_nz : forall n, (0 < n)%nat -> ~ inject_Z (Z.of_nat n) == 0.
Proof. intros n Hn Heq. unfold Qeq in Heq; simpl in Heq; lia. Qed.

(* linearity of expectation *)
Lemma E_add : forall A (f g : A -> nat) l,
  E (fun a => (f a + g a)%nat) l == E f l + E g l.
Proof.
  intros A f g l. unfold E. rewrite list_sum_map_add, Nat2Z.inj_add, inject_Z_plus.
  apply q_div_add.
Qed.

Lemma E_const : forall A c (l : list A),
  (0 < length l)%nat -> E (fun _ => c) l == inject_Z (Z.of_nat c).
Proof.
  intros A c l Hl. unfold E. rewrite list_sum_map_const, Nat2Z.inj_mul, inject_Z_mult.
  field. now apply inj_nz.
Qed.

(* linearity over a finite family of cost components *)
Lemma E_linear_sum : forall A (comp : nat -> A -> nat) (js : list nat) (l : list A),
  (0 < length l)%nat ->
  E (fun a => list_sum (map (fun j => comp j a) js)) l
    == qsumQ (map (fun j => E (comp j) l) js).
Proof.
  intros A comp js l Hl. induction js as [|j js IH]; cbn [map list_sum qsumQ].
  - rewrite (E_const A 0 l Hl). reflexivity.
  - rewrite <- IH. apply E_add.
Qed.
