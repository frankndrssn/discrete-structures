(*** CS 191 - Final exam *)

(** * Read the following instructions carefully *)

(** Do not modify code in the (****) blocks or the grader will not
    work correctly and you will get a 0. Please note that modifying
    problem definitions to fool the grader is an academic integrity
    violation. *)

(** Read the instructions in the exam pdf carefully. The exam pdf is
    available on Piazza and the course website. There are 8 problems
    in total. The deadline is the 10th of May @ 14:00. Late submissions
    will not be accepted. *)

(******************************************************************************)
Require Import Arith.
(******************************************************************************)



(** Problem 1 *)
Lemma prob1 : forall A B C D : Prop,
    (A -> B) ->
    (A -> C) ->
    (B -> C -> D) ->
    A -> D.
Proof.
  intros A B C D f g h a.
  apply h.
  - apply f.
    exact a.
  - apply g.
    exact a.
Qed.

(** Problem 2 *)
Lemma prob2 : forall P Q : Prop,
    (P \/ ~ P) -> (((P -> Q) -> P) -> P).
Proof.
  intros P Q [p | np] f.
  - exact p.
  - apply f.
    intros p.
    contradiction.
Qed.

(** Problem 3 *)
(* You may find the tactic [exfalso] useful. *)
Lemma prob3 :
  (forall P : Prop, ~ P \/ P) ->
  (forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q).
Proof.
  intros f P Q npq.
  destruct (f P) as [np | p].
  - left.
    exact np.
  - destruct (f Q) as [nq | q].
    + right.
      exact nq.
    + exfalso.
      apply npq.
      split.
      * exact p.
      * exact q.
Qed.



(******************************************************************************)
Inductive acc : nat -> Prop :=
| acc_k : forall k, (forall y, y < k -> acc y) -> acc k.

Theorem lt_wf : forall n, acc n.
Proof.
  induction n.
  - constructor.
    intros y con.
    inversion con.
  - destruct IHn.
    constructor.
    intros y1 lt1.
    constructor.
    intros y2 lt2.
    constructor.
    intros y3 lt3.
    apply H.
    apply Nat.le_trans with (m := y2).
    + exact lt3.
    + apply Nat.le_trans with (m := y1).
      * apply Nat.lt_le_incl.
        exact lt2.
      * apply le_S_n.
        exact lt1.
Qed.

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
    (forall x, (forall y, y < x -> P y) -> P x) ->
    forall x, P x.
Proof.
  refine (fun P f x => _).
  refine (acc_then_Px _ f _).
  apply lt_wf.
Defined.

Inductive div4 : nat -> Prop :=
| div4_0 : div4 0
| div4_S : forall n, rem2 n -> div4 (S (S n))
with rem2 : nat -> Prop :=
| rem2_S : forall n, div4 n -> rem2 (S (S n)).

Lemma div_ss_rem :
  forall n, div4 (S (S n)) -> rem2 n.
Proof.
  intros n div.
  inversion div.
  assumption.
Qed.

Lemma rem_ss_div :
  forall n, rem2 (S (S n)) -> div4 n.
Proof.
  intros n rem.
  inversion rem.
  assumption.
Qed.

Lemma not_rem_0 : ~ rem2 0.
Proof.
  intros rem.
  inversion rem.
Qed.

Lemma not_div_1 : ~ div4 1.
Proof.
  intros div.
  inversion div.
Qed.
(******************************************************************************)



(** Problem 4 *)
(* You may find [not_rem_0], [not_div_1],
   [div_ss_rem], and [rem_ss_div] helpful. *)
Lemma prob4 :
  forall n, div4 n -> ~ rem2 n.
Proof.
  induction n using strong_nat_ind.
  intros div rem.
  destruct n as [|[|]].
  - apply not_rem_0 in rem.
    contradiction.
  - apply not_div_1 in div.
    contradiction.
  - apply div_ss_rem in div.
    apply rem_ss_div in rem.
    apply H in rem.
    + contradiction.
    + repeat constructor.
Qed.



(******************************************************************************)
Definition relation (X Y : Type) := X -> Y -> Prop.
Definition partial_function {X Y : Type} (R : relation X Y) :=
  forall (x : X) (y1 y2 : Y), R x y1 -> R x y2 -> y1 = y2.
(******************************************************************************)



(** Problem 5 *)
Lemma prob5 : ~ partial_function le.
Proof.
  intros ple.
  set (con := ple 0 1 2).
  discriminate con.
  - repeat constructor.
  - repeat constructor.
Qed.



(******************************************************************************)
Variable (choice : forall {A P} (prf : exists a : A, P a), A).
Hypothesis (choice_ok : 
             forall {A P} (prf : exists a : A, P a), P (choice prf)).

Record Func (dom cod : Type) : Type :=
  mkFunc {
      rel : dom -> cod -> Prop
    ; total : forall x : dom, exists y : cod, rel x y
    ; functional : forall x : dom, forall y z : cod, rel x y -> rel x z -> y = z
    }.

Definition app : forall {dom cod}, Func dom cod -> dom -> cod.
Proof.
  intros dom cod f x.
  exact (choice (f.(total dom cod) x)).
Defined.

Definition by_formula : forall {dom cod : Type}, (dom -> cod) -> Func dom cod.
Proof.
  intros dom cod f.
  refine (mkFunc dom cod (fun x y => f x = y) _ _).
  - intros x.
    exists (f x).
    reflexivity.
  - intros x y z eq1 eq2.
    rewrite <- eq1.
    rewrite <- eq2.
    reflexivity.
Defined.

Lemma by_formula_ok : forall {dom cod : Type} (formula : dom -> cod) (x : dom),
    app (by_formula formula) x = formula x.
Proof.
  intros dom cod formula x.
  unfold by_formula.
  unfold app.
  simpl.
  set (ok := choice_ok
               (ex_intro (fun y : cod => formula x = y) (formula x) eq_refl)).
  symmetry.
  exact ok.
Qed.

Definition surjective {dom cod} (f : Func dom cod) :=
  forall y : cod, exists x : dom, app f x = y.

Definition injective {dom cod} (f : Func dom cod) :=
  forall x x' : dom, app f x = app f x' -> x = x'.

Definition f := by_formula (fun x => 5 * x + 1).

Lemma f_ok :
  forall x, app f x = 5 * x + 1.
Proof.
  intros x.
  unfold f.
  rewrite by_formula_ok.
  reflexivity.
Qed.
(******************************************************************************)



(** Problem 6 *)
(** The function [f : nat -> nat] is defined by the formula [f x = 5 * x + 1].
 You may find [f_ok] useful. *)
Lemma prob6 : injective f /\ ~ surjective f.
Proof.
  split.
  - intros a b eq.
    repeat rewrite f_ok in eq.
    rewrite Nat.add_cancel_r in eq.
    rewrite Nat.mul_cancel_l in eq.
    + exact eq.
    + discriminate.
  - intros sur.
    destruct (sur 0) as [x eq].
    rewrite f_ok in eq.
    rewrite Nat.add_1_r in eq.
    discriminate.
Qed.



(******************************************************************************)
Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Lemma div_add : forall a b c,
    (a | b) -> (a | c) -> (a | b + c).
Proof.
  intros a b c [x eq] [y eq'].
  exists (x + y).
  ring_simplify.
  subst.
  reflexivity.
Qed.
(******************************************************************************)



(** Problem 7 *)
(* You may find [div_add] helpful. *)
Lemma prob7 : forall a b c, (a | c) -> (b | c) -> Zis_gcd a b 1 -> (a * b | c).
Proof.
  intros a b c div1 div2 gcd.
  destruct div1 as [x eq].
  destruct div2 as [y eq'].
  apply Zis_gcd_mult with (c := c) in gcd.
  ring_simplify in gcd.
  apply Zis_gcd_bezout in gcd.
  destruct gcd.
  rewrite <- H.
  apply div_add.
  - exists (u * y).
    rewrite eq'.
    ring.
  - exists (v * x).
    rewrite eq.
    ring.
Qed.



(******************************************************************************)
Definition reflexive {X : Type} (R : relation X X) :=
  forall x : X, R x x.
Definition symmetric {X : Type} (R : relation X X) :=
  forall x x' : X, R x x' -> R x' x.
Definition transitive {X : Type} (R : relation X X) :=
  forall a b c : X, R a b -> R b c -> R a c.
Definition equivalence {X : Type} (R : relation X X) :=
  reflexive R /\ symmetric R /\ transitive R.
Definition congruence (a b c : Z) := (a | (b - c)).
(******************************************************************************)



(** Problem 8 *)
Lemma prob8 : forall a : Z, equivalence (congruence a).
Proof.
  intros a.
  split; [| split].
  - intros x.
    exists 0.
    rewrite Z.sub_diag.
    reflexivity.
  - intros x y [z eq].
    exists (-z).
    rewrite <- Zopp_mult_distr_l.
    rewrite <- eq.
    ring.
  - intros x y z [u eq] [v eq'].
    exists (u + v).
    assert (h : x - y + (y - z) = x - z). {
      ring.
    }
    rewrite <- h.
    rewrite eq.
    rewrite eq'.
    ring.
Qed.



(******************************************************************************)
Close Scope Z_scope.
(******************************************************************************)
