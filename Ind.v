Require Import Arith.
Module Type Induction.
(** * Inductive data types and induction
*)
(**
   The type of natural numbers is inductively defined by two rules:
   - [O] is a natural number
   - if [n] is a natural number then [S n] is a natural number.
   We write [0] for [O], [1] for [S O], [2] for [S (S O)], etc.
 *)
Print nat.

(**
   Inductively defined data types admit induction (elimination)
   principles. The induction principle of a data type
   tells us how to use an element of that type.
 *)
Check nat_ind.

(**
   In fact, [True], [False], [/\], [\/], [exists], and [=] are inductive types in Coq
   whose induction principles we have been taking for granted.
 *)
Print True.
(* [Inductive True : Prop :=  I : True.] *)
Check True_ind.
(* [True_ind : forall P : Prop, P -> True -> P] *)

Print False.
(* [Inductive False : Prop :=  .] *)
Check False_ind.
(* [False_ind : forall P : Prop, False -> P] *)

Print "/\".
(* [Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B.] *)
Check and_ind.
(* [and_ind : forall A B P : Prop, (A -> B -> P) -> A /\ B -> P] *)

Print "\/".
(* [Inductive or (A B : Prop) : Prop :=
    or_introl : A -> A \/ B | or_intror : B -> A \/ B.] *)
Check or_ind.
(* [or_ind
     : forall A B P : Prop, (A -> P) -> (B -> P) -> A \/ B -> P] *)

Print ex.
(* [Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> exists y, P y.] *)
Check ex_ind.
(* [ex_ind
     : forall (A : Type) (P : A -> Prop) (P0 : Prop),
       (forall x : A, P x -> P0) -> (exists y, P y) -> P0] *)

Print "=".
(* [Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x.] *)
Check eq_ind.
(* [eq_ind
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y] *)

Check nat_ind.

(**
   We can define various functions in terms of the induction principle,
   although we need to use [nat_rect] here for a technical reason
   that we will not discuss.
 *)
Definition add' : nat -> nat -> nat :=
  nat_rect (fun m => nat -> nat) (fun m => m) (fun _ f m => S (f m)).

(**
   Programming with induction principles directly is difficult.
   Coq (and many other good languages) allows definition by
   _pattern matching_.
 *)
Fixpoint add'' (n : nat) (m : nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (add'' n' m)
  end.

(**
   Indeed, [add'] and [add''] compute the same result.
   We can prove this by induction.
 *)
Theorem add'_eq_add'' :
  forall n m, add' n m = add'' n m.
Proof.
  set (P := fun n => forall m, add' n m = add'' n m).
  apply (nat_ind P).
  - unfold P.
    intros m.
    simpl.
    reflexivity.
  - unfold P.
    intros n IH m.
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(**
   Coq offers the [induction] tactic that applies the appropriate
   induction principle automatically. The [induction] tactic
   also finds a _motive of induction_ automatically.
 *)
Theorem add'_eq_add''_better :
  forall n m, add' n m = add'' n m.
Proof.
  induction n.
  - intros m.
    simpl.
    reflexivity.
  - intros m.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

(**
   We can write a simple program that decides whether two natural
   numbers are equal.
 *)
Fixpoint nat_eq (n : nat) (m : nat) : Prop :=
  match n, m with
  | 0, 0 => True
  | 0, S m => False
  | S n, 0 => False
  | S n, S m => nat_eq n m
  end.

(**
   The correctness of this program is proven in the following
   two lemmas.
 *)
Lemma eq_then_nat_eq :
  forall n m, n = m -> nat_eq n m.
Proof.
  intros n m eq.
  rewrite eq.
  clear eq.
  induction m.
  - simpl.
    trivial.
  - simpl.
    exact IHm.
Qed.

Lemma nat_eq_then_eq :
  forall n m, nat_eq n m -> n = m.
Proof.
  induction n.
  - induction m.
    + intros _.
      reflexivity.
    + intros H.
      simpl in H.
      contradiction.
  - induction m.
    + intros H.
      simpl in H.
      contradiction.
    + intros H.
      simpl in H.
      apply IHn in H.
      rewrite H.
      reflexivity.
Qed.

(**
   This simple program allows us to prove a number of theorems
   about natural numbers. We can now prove that the successor
   function [S] is injective, and that [0] is not the successor
   of any natural number.
 *)
Theorem suc_inj : forall n m, S n = S m -> n = m.
Proof.
  intros n m eq.
  apply eq_then_nat_eq in eq.
  apply nat_eq_then_eq.
  simpl in eq.
  exact eq.
Qed.

Theorem O_neq_suc : forall n, 0 <> S n.
Proof.
  unfold not.
  intros n eq.
  apply eq_then_nat_eq in eq.
  simpl in eq.
  contradiction.
Qed.

(**
   We can use induction to prove many other properties of
   the natural numbers.
 *)

Theorem add_comm : forall n m, n + m = m + n.
Proof.
  induction n.
  - induction m.
    + reflexivity.
    + simpl.
      rewrite <- IHm.
      reflexivity.
  - induction m.
    + simpl.
      rewrite IHn.
      simpl.
      reflexivity.
    + simpl.
      rewrite IHn.
      rewrite <- IHm.
      simpl.
      rewrite IHn.
      reflexivity.
Qed.

Theorem zero_add : forall n, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem add_zero : forall n, n + 0 = n.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem suc_add_one : forall n, S n = n + 1.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem add_assoc : forall a b c, a + (b + c) = (a + b) + c.
Proof.
  induction a.
  - intros b c.
    reflexivity.
  - intros b c.
    simpl.
    rewrite IHa.
    reflexivity.
Qed.

(** * Additional inductive data type examples
 *)
(**
   A (natural number) binary tree is either a [leaf] or a
   [node] consisting of a left subtree [l], a value [n], and
   a right subtree [r].
 *)
Inductive btree : Type :=
| leaf : btree
| node (l : btree) (n : nat) (r : btree) : btree.

(**
   Of course, [btree] admits an induction principle.
 *)
Check btree_ind.
(* btree_ind
     : forall P : btree -> Prop,
       P leaf ->
       (forall l : btree, P l -> forall (n : nat) (r : btree),
               P r -> P (node l n r)) ->
       forall b : btree, P b *)

(**
   We can now define a few operations on [btree].
   [size t] is the number of nodes in [t], and
   [reverse t] simply flips [t].
 *)
Fixpoint size (t : btree) : nat :=
  match t with
  | leaf => 0
  | node l n r => S (size l + size r)
  end.
  
Fixpoint reverse (t : btree) : btree :=
  match t with
  | leaf => leaf
  | node l n r => node (reverse r) n (reverse l)
  end.

(**
   We can prove that [reverse] is _involutive_, i.e.,
   reversing a tree twice is the same as doing nothing.
 *)
Theorem reverse_involutive :
  forall t, reverse (reverse t) = t.
Proof.
  induction t.
  - simpl.
    reflexivity.
  - simpl (reverse (node t1 n t2)).
    simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

(**
   And [reverse] does not change the number of nodes in a tree.
 *)
Theorem reverse_same_size :
  forall t, size (reverse t) = size t.
Proof.
  induction t.
  - simpl.
    reflexivity.
  - simpl (reverse (node t1 n t2)).
    simpl.
    rewrite IHt2.
    rewrite IHt1.
    ring.
Qed.

(**
   The examples we have seen thus far admit simple induction
   proofs. We just do a straightforward induction on one of
   the variables. There are examples where we need to be a bit
   more clever.
 *)

(**
   Suppose that you want to build a computer system with any amount of
   storage subject to the following constraints
   - The system must have at least 2TB of storage.
   - You only have access to any number of
     2TB or 3TB hard disks.
   If we can prove the following theorem, then it is always possible to
   build such a computer system. We can try to do an induction on [n].
 *)
Theorem storage :
  forall n, exists i j, n + 2 = 2 * i + 3 * j.
Proof.
  induction n.
  - exists 1.
    exists 0.
    simpl.
    reflexivity.
  - destruct IHn as [i [j eq]].
    simpl.
    (* We can't make 1TB of storage out of
     2TB and 3TB disks. If we know how to build
     a system with capacity [n + 1], then we can
     build this system by adding a 2TB disk.
     However, the induction hypothesis does not
     tell us how to do that. We are stuck.
     *)
Abort.

(**
   The obvious induction does not work. However, this
   does not necessarily mean that the theorem is not
   provable. Perhaps, We are just not smart enough.
   In this case, [storage] is in fact provable by
   induction. Before we prove it, we need to define
   the [<=] relation.
 *)

(**
   In Coq, the [<=] relation is defined inductively.
 *)
Print le.
(* [Inductive le (n : nat) : nat -> Prop :=
    le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m.] *)

(**
   This definition says that the only canonical ways to construct
   a proof of [n <= m] are
   - we already know [n = m], so we can use the constructor [le_n].
   - we know some number [k] so that [n <= k] and [S k = m], so
      we can use the constructor [le_S].
  Thus, if we know that [n <= m] then we should be able to infer that
  either [n = m] or there is some [k] so that [n <= k] and [S k = m].
  This is an inversion principle for the inductive type [<=].
  Indeed, we can prove the inversion principle using induction.
 *)
Theorem le_inversion' :
  forall n m, n <= m -> (n = m) \/ (exists k, n <= k /\ S k = m).
Proof.
  intros n m le.
  induction le.
  - left.
    reflexivity.
  - destruct IHle as [eq | ex].
    + right.
      exists n.
      split.
      * apply le_n.
      * rewrite eq.
        reflexivity.
    + right.
      destruct ex as [k [le' eq]].
      exists (S k).
      split.
      * apply le_S.
        exact le'.
      * rewrite eq.
        reflexivity.
Qed.

(**
   We can use this inversion principle to prove that
   [S n <= 0] never holds for any natural number [n].
 *)
Theorem suc_not_le0' :
  forall n, ~(S n <= 0).
Proof.
  unfold not.
  intros n le.
  apply le_inversion' in le.
  destruct le as [eq | ex].
  - symmetry in eq.
    apply (O_neq_suc n).
    exact eq.
  - destruct ex as [k [_ eq]].
    symmetry in eq.
    apply (O_neq_suc k).
    exact eq.
Qed.

(**
   Coq already knows this inversion principle and provides
   the [inversion] tactic.
 *)
Theorem le_inversion :
  forall n m, n <= m -> (n = m) \/ (exists k, n <= k /\ S k = m).
Proof.
  intros n m le.
  inversion le.
  - left.
    reflexivity.
  - right.
    exists m0.
    split.
    + exact H.
    + reflexivity.
Qed.

(**
   The [inversion] tactic does quite a number of things
   for us. [suc_not_le0'] admits another proof that is
   quite trivial with the [inversion] tactic.
 *)
Theorem suc_not_le0 :
  forall n, ~(S n <= 0).
Proof.
  unfold not.
  intros n le.
  inversion le.
Qed.


(**
   We can use the inversion principle along with induction
   to prove that the [<=] relation is _transitive_ and
   _antisymmetric_.
 *)
Theorem le_transitive :
  forall a b c, a <= b -> b <= c -> a <= c.
Proof.
  intros a b c le le'.
  induction c.
  - inversion le'.
    rewrite H in le.
    inversion le.
    apply le_n.
  - inversion le'.
    + rewrite H in le.
      exact le.
    + apply le_S.
      apply IHc.
      exact H0.
Qed.

(**
   Before proving antisymmetry, we record some general facts about [<=].
 *)
Theorem suc_monotone :
  forall n m, n <= m -> S n <= S m.
Proof.
  intros n m le.
  induction le.
  - apply le_n.
  - apply le_S.
    exact IHle.
Qed.

Theorem suc_inv_monotone :
  forall n m, S n <= S m -> n <= m.
Proof.
  intros n.
  induction m.
  - intros le.
    inversion le.
    + apply le_n.
    + inversion H0.
  - intros le.
    inversion le.
    + apply le_n.
    + apply IHm in H0.
      apply le_transitive with (b := m).
      * exact H0.
      * apply le_S.
        apply le_n.
Qed.

Theorem suc_not_le :
  forall {n}, ~ (S n <= n).
Proof.
  unfold not.
  intros n le.
  induction n.
  - inversion le.
  - apply IHn.
    apply suc_inv_monotone.
    exact le.
Qed.

(**
   Now, we can prove antisymmetry.
 *)
Theorem le_antisymmetric :
  forall n m, n <= m -> m <= n -> n = m.
Proof.
  intros n m le le'.
  inversion le.
  - reflexivity.
  - inversion le'.
    + rewrite H0.
      symmetry.
      exact H1.
    + subst.
      clear le le'.
      assert (con : S m1 <= m1).
      {
        apply le_transitive with (b := m0).
        - exact H.
        - apply le_transitive with (b := S m0).
          + apply le_S.
            apply le_n.
          + exact H1.
      }
      set (con' := suc_not_le con).
      contradiction.
Qed.
      
(**
   The [<] relation is defined in terms of [<=].
 *)
Print lt.
(* [lt = fun n m : nat => S n <= m
     : nat -> nat -> Prop] *)

(**
   Of course, [n < m] implies that [n <= m].
 *)
Theorem lt_then_le :
  forall n m, n < m -> n <= m.
Proof.
  intros n m lt.
  induction lt.
  - apply le_S.
    apply le_n.
  - apply le_S.
    exact IHlt.
Qed.

(**
   To prove [storage] we first prove a small lemma.
   The idea is to prove [storage] up to some limit [m].
   We can do induction on [m] to show that [storage]
   holds for any upper limit [m].
 *)
Lemma storage' :
  forall m n, n < m -> exists i j, n + 2 = 2 * i + 3 * j.
Proof.
  induction m.
  - intros n lt.
    inversion lt.
  - intros n lt.
    destruct n.
    + exists 1.
      exists 0.
      simpl.
      reflexivity.
    + destruct n.
      * exists 0.
        exists 1.
        simpl.
        reflexivity.
      * set (f := IHm n).
        assert (lt' : n < m).
        {
          apply le_transitive with (b := S n).
          - apply le_n.
          - apply le_S_n.
            apply lt_then_le.
            exact lt.
        }
        apply f in lt'.
        destruct lt' as [i [j eq]].
        exists (i + 1).
        exists j.
        simpl.
        rewrite eq.
        ring.
Qed.

(**
   [storage] is now a simple corollary of [storage'].
 *)
Theorem storage :
  forall n, exists i j, n + 2 = 2 * i + 3 * j.
Proof.
  intros n.
  apply storage' with (m := S n).
  apply le_n.
Qed.

(**
   We can assemble this kind of argument into a new induction principle
   called _strong induction_. First, we need a few definitions.
 *)

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
    apply le_transitive with (b := y').
    + exact lt''.
    + apply le_transitive with (b := y).
      * apply lt_then_le.
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
   We can prove [storage] using [strong_nat_ind].
 *)
Theorem storage_str :
  forall n, exists i j, n + 2 = 2 * i + 3 * j.
Proof.
  induction n using strong_nat_ind.
  destruct n.
  - exists 1, 0.
    ring.
  - destruct n.
    + exists 0, 1.
      ring.
    + assert (h : n < S (S n)). {
        constructor.
        constructor.
      }
      apply H in h.
      destruct h as [i [j eq]].
      exists (S i), j.
      assert (h : n + 2 = S (S n)). {
        ring.
      }
      rewrite <- h.
      rewrite eq.
      ring.
Qed.

(** * Additional examples
 *)
(**
   A natural number [n] is _even_ if
   there is some [k] such that [n = 2 * k].
   Otherwise, it is said to be _odd_.
 *)
Definition even (n : nat) : Prop :=
  exists k, n = 2 * k.

Definition odd (n : nat) : Prop :=
  ~ (even n).

Example even0 : even 0.
Proof.
  exists 0.
  reflexivity.
Qed.

Example odd1 : odd 1.
Proof.
  intros [k eq].
  destruct k.
  - discriminate.
  - simpl in eq.
    injection eq.
    intros eq'.
    rewrite add_comm in eq'.
    simpl in eq'.
    discriminate.
Qed.

(**
   Some facts about [even] and [odd].
 *)
Theorem even_even_suc_suc :
  forall n, even n -> even (S (S n)).
Proof.
  intros n en.
  unfold even in en.
  destruct en as [k eq].
  unfold even.
  rewrite eq.
  exists (k + 1).
  ring.
Qed.

Theorem even_suc_suc_even :
  forall n, even (S (S n)) -> even n.
Proof.
  intros n [k eq].
  destruct k.
  - discriminate.
  - exists k.
    simpl in eq.
    injection eq.
    intros eq'.
    rewrite add_comm in eq'.
    simpl in eq'.
    injection eq'.
    intros eq''.
    rewrite eq''.
    ring.
Qed.

Theorem odd_odd_suc_suc :
  forall n, odd n -> odd (S (S n)).
Proof.
  intros n o oss.
  apply even_suc_suc_even in oss.
  contradiction.
Qed.

Theorem odd_suc_suc_odd :
  forall n, odd (S (S n)) -> odd n.
Proof.
  intros n oss e.
  apply even_even_suc_suc in e.
  contradiction.
Qed.

Example even2 : even 2.
Proof.
  apply even_even_suc_suc.
  exact even0.
Qed.

Example odd3 : odd 3.
Proof.
  apply odd_odd_suc_suc.
  exact odd1.
Qed.

Theorem even_then_suc_odd :
  forall n, even n -> odd (S n).
Proof.
  induction n.
  - intros _.
    exact odd1.
  - intros es ess.
    apply even_suc_suc_even in ess.
    apply IHn in ess.
    contradiction.
Qed.

Theorem odd_then_suc_even :
  forall n, odd n -> even (S n).
Proof.
  induction n using strong_nat_ind.
  destruct n.
  - intros o0.
    set (e0 := even0).
    contradiction.
  - destruct n.
    + intros o1.
      exact even2.
    + intros oss.
      assert (h : n < S (S n)). {
        repeat constructor.
      }
      apply H in h.
      * apply even_even_suc_suc.
        exact h.
      * apply odd_suc_suc_odd.
        exact oss.
Qed.

Theorem odd_odd_even :
  forall n m, odd n -> odd m -> even (n + m).
Proof.
  induction n using strong_nat_ind.
  intros m on om.
  destruct n.
  - set (e0 := even0).
    contradiction.
  - destruct n.
    + simpl.
      apply odd_then_suc_even.
      exact om.
    + assert (h : n < S (S n)). {
        repeat constructor.
      }
      apply H with (m := m) in h.
      * simpl.
        apply even_even_suc_suc.
        exact h.
      * apply odd_suc_suc_odd.
        exact on.
      * exact om.
Qed.

Theorem even_odd_odd :
  forall n m, even n -> odd m -> odd (n + m).
Proof.
  induction n using strong_nat_ind.
  intros m en om e.
  destruct n.
  - simpl in e.
    contradiction.
  - destruct n.
    + set (o1 := odd1).
      contradiction.
    + assert (h : n < S (S n)). {
        repeat constructor.
      }
      apply even_suc_suc_even in en.
      set (h' := H n h m en om).
      simpl in e.
      apply even_suc_suc_even in e.
      contradiction.
Qed.

End Induction.
