Require Import Arith.

(**
   A natural number [k] is said to be _accessible_
   (with respect to the [<] relation) if every natural
   number [< k] is accessible.
 *)
Inductive acc : nat -> Prop :=
  acc_k : forall k, (forall y, y < k -> acc y) -> acc k.

(**
   In fact, every natural number is accessible with respect to
   the [<] relation, i.e., [<] is a _well founded_ relation.
 *)
Theorem lt_wf : forall n, acc n.
Proof.
  induction n.
  - apply acc_k.
    intros y con.
    inversion con.
  - induction IHn.
    clear H0.
    apply acc_k.
    intros y lt.
    apply acc_k.
    intros y' lt'.
    apply acc_k.
    intros y'' lt''.
    apply H.
    apply le_trans with (m := y').
    + exact lt''.
    + apply le_trans with (m := y).
      * apply lt_le_weak.
        exact lt'.
      * apply le_S_n.
        exact lt.
Qed.

(**
   We can use the accessibility relation to define
   the strong induction principle for the natural numbers.
 *)
Definition acc_then_Px :
  forall {P : nat -> Prop} (n : nat),
    (forall x, (forall y, y < x -> P y) -> P x)
    -> acc n
    -> P n.
Proof.
  refine (fun P n f acc => acc_ind _ _ _ _).
  - intros k _ f'.
    apply f.
    exact f'.
  - exact acc.
Defined.

Definition strong_nat_ind :
  forall P : nat -> Prop,
    (forall x, (forall y, y < x -> P y) -> P x)
    -> forall x, P x.
Proof.
  refine (fun P f x => _).
  refine (acc_then_Px _ f _).
  apply lt_wf.
Defined.
    
(**
   In terms of what can be proved, strong induction and
   regular induction have the same strength. In fact, we
   defined strong induction completely in terms of regular
   induction. The only difference is that strong induction
   gives us a stronger induction hypothesis, making
   proofs more convenient sometimes.
 *)

(** * Homework problems
    Instructions:
    - When appropriate, you should make use of theorems
      in this module.
    - You should gain the big picture (e.g., write an
      informal proof) before you start working on the
      Coq proof.
    - The assignment does not require esoteric tactics
      (e.g., [pattern], [refine], [fold], etc) that are
      not discussed in class.
    - Replace [Abort.] with [Qed.] after you successfully solve a problem.
    - If you can't solve a problem, comment out your code (if any) and
      end the problem with [Abort.] instead of [Qed.] In Coq, the
      syntax for comment is [(* comment goes here *)].
    - The number of submissions is unlimited.
    - Deadline: Apr 18 @ 23:55
 *)

Fixpoint sum_n2 n :=
  match n with
  | 0 => 0
  | S p => n * n + sum_n2 p
  end.

(** Use induction to prove that *)
Theorem sum_square_p :
  forall n, 6 * sum_n2 n = n * (n + 1) * (2 * n + 1).
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl (sum_n2 (S n)).
    ring_simplify.
    rewrite IHn.
    ring.
Qed.

Fixpoint sum_odd_n n :=
  match n with
  | 0 => 0
  | S p => 1 + 2 * p + sum_odd_n p
  end.

(** Prove that the sum of the first n odd natural numbers is n^2 *)
Theorem odd_sum : forall n, sum_odd_n n = n * n.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    ring_simplify.
    rewrite IHn.
    ring.
Qed.

(** Use strong induction to prove that any number greater than
    seven can be written as a sum of multiples of three and five. *)
Theorem three_and_five : forall n, exists a b, n + 8 = 3 * a + 5 * b.
Proof.
  induction n using strong_nat_ind.
  destruct n as [|[|[|]]].
  - exists 1, 1.
    reflexivity.
  - exists 3, 0.
    reflexivity.
  - exists 0, 2.
    reflexivity.
  - assert (h : n < S (S (S n))). {
      repeat constructor.
    }
    apply H in h.
    destruct h as [a [b eq]].
    exists (S a), b.
    ring_simplify.
    rewrite <- eq.
    ring.
Qed.
