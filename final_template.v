(*** CS 191 - Final exam *)

(** * Read the following instructions carefully *)

(** Do not modify code in the (****) blocks. Please note that modifying
    problem definitions is an academic integrity violation. *)

(** Read the instructions in the exam pdf carefully. The exam pdf is
    available on Piazza and the course website.  *)

(** There are 8 problems in total. *)

(** The deadline is the 10th of May @ 14:00. Late submissions
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
  (* ... *)
Abort.

(** Problem 2 *)
Lemma prob2 : forall P Q : Prop,
    (P \/ ~ P) -> (((P -> Q) -> P) -> P).
Proof.
  (* ... *)
Abort.

(** Problem 3 *)
(* You may find the tactic [exfalso] useful. *)
Lemma prob3 :
  (forall P : Prop, ~ P \/ P) ->
  (forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q).
Proof.
  (* ... *)
Abort.



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
(* The intended interpretation of [div4] is the
 usual divisibility by 4 relation and the intended
 interpretation of [rem2] is [rem2 n <-> n mod 4 = 2]. *)
(* Proving that these relations agree with their
   intended interpretations is a difficult exercise, so
   we will ask you to prove a simpler "sanity-check"
   lemma. *)
(* Show that if [n] satisfies [div4] then it does not
 satisfy [rem2]. *)
(* You may find [not_rem_0], [not_div_1],
   [div_ss_rem], and [rem_ss_div] helpful. *)
Lemma prob4 :
  forall n, div4 n -> ~ rem2 n.
Proof.
  Check not_rem_0.
  Check not_div_1.
  Check div_ss_rem.
  Check rem_ss_div.
  induction n using strong_nat_ind.
  (* ... *)
Abort.



(******************************************************************************)
Definition relation (X Y : Type) := X -> Y -> Prop.
Definition partial_function {X Y : Type} (R : relation X Y) :=
  forall (x : X) (y1 y2 : Y), R x y1 -> R x y2 -> y1 = y2.
(******************************************************************************)



(** Problem 5 *)
Lemma prob5 : ~ partial_function le.
Proof.
  (* ... *)
Abort.



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
(* The function [f : nat -> nat] is defined by the formula [f x = 5 * x + 1].
 You may find [f_ok] useful. *)
Lemma prob6 : injective f /\ ~ surjective f.
Proof.
  Check f_ok.
  (* ... *)
Abort.



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
(* You may find [Zis_gcd_bezout] and [div_add] helpful.
 When you have a hypothesis [h : Bezout a b d], you can
 [destruct] it. *)
Lemma prob7 : forall a b c, (a | c) -> (b | c) -> Zis_gcd a b 1 -> (a * b | c).
Proof.
  Check Zis_gcd_bezout.
  Check div_add.
  (* ... *)
Abort.



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
  (* ... *)
Abort.



(******************************************************************************)
Close Scope Z_scope.
(******************************************************************************)
