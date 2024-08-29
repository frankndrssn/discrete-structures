Require Import Bool.Bool.
Require Import Arith.

(** Do not modify this block. Review questions start at line 402. *)
(******************************************************************************)

(**
   Functions as relations.
 *)
Variable (choice : forall {A P} (prf : exists a : A, P a), A).
Hypothesis (choice_ok : 
             forall {A P} (prf : exists a : A, P a), P (choice prf)).

(**
     Functions can be realized as special binary relations.
     To specify a function from [dom] to [cod], specify
     a binary relation that is total and functional.
     Intuitively, [rel x y] means when we evaluate the function at [x]
     then the output is [y].
 *)
Record Func (dom cod : Type) : Type :=
  mkFunc {
      rel : dom -> cod -> Prop
    ; total : forall x : dom, exists y : cod, rel x y
    ; functional : forall x : dom, forall y z : cod, rel x y -> rel x z -> y = z
    }.

(**
     Totality says for any [x] in [dom] there is some [y] in [cod]
     such that [rel x y]. Thus, a natural notion of function application is
     to map [x] to [y].
 *)
Definition app : forall {dom cod}, Func dom cod -> dom -> cod.
Proof.
  intros dom cod f x.
  exact (choice (f.(total dom cod) x)).
Defined.

(**
     Often, we define functions by "formulas". For example, we often
     write
     [[
     x ↦ x + 1
     ]]
     or
     [[
     f(x) = x + 1
     ]]
     to define a function that maps the input [x] to the output [x + 1].
     This always yields a function in the sense introduced in the
     beginning of this module.
 *)
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

(**
     Of course, the function defined by [by_formula] must agree with the given
     formula. For example, when I evaluate the function defined by
     [[
     x ↦ x + 1
     ]]
     at [1], I should get [2].
 *)
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

(**
     We consider two functions
     [[
     f, g : dom → cod
     ]]
     equal if they have the same IO behavior:
     they map the same input to the same output.
     This is called _functional extensionality_.
     Extensionality means that we don't care about the
     internals of the function. For example, the functions
     [[
     f(x) = 2(x + 1) and g(x) = 2x + 2
     ]]
     are equal (because they have the same IO behavior)
     even though their internals are different (they are defined
     by different formulas.)
 *)
Hypothesis funext : forall {dom cod} (f g : Func dom cod),
    (forall x : dom, app f x = app g x) -> f = g.

(**
     Given a function that maps elements of [A] to elements of [B]
     and a function that maps elements of [B] to elements of [C], we
     can compose these two functions, yielding a function that maps
     elements of [A] to elements of [C]. Function composition is given
     by the following formula:
     [[
     x ↦ app g (app f x)
     ]]
 *)
Definition comp : forall {A B C}, Func B C -> Func A B -> Func A C.
Proof.
  intros A B C g f.
  exact (by_formula (fun a => app g (app f a))).
Defined.

(**
     For any two composable functions, the composite agrees with the
     formula given above. This is a simple corollary of [by_formula_ok].
 *)
Corollary comp_ok : forall {A B C} (g : Func B C) (f : Func A B) (a : A),
    app (comp g f) a = app g (app f a).
Proof.
  intros A B C g f a.
  unfold comp.
  rewrite by_formula_ok.
  reflexivity.
Qed.

(**
     Function composition is associative.
 *)
Lemma comp_assoc : forall {A B C D} (f : Func C D) (g : Func B C) (h : Func A B),
    comp f (comp g h) = comp (comp f g) h.
Proof.
  intros A B C D f g h.
  apply funext.
  intros a.
  rewrite comp_ok.
  rewrite comp_ok.
  rewrite comp_ok.
  rewrite comp_ok.
  reflexivity.
Qed.

(**
     The identity function is sort of like a no-op in CS.
     Given an element of [A], the identity function on [A] simply
     outputs the input without doing anything to it.
     It is defined by the formula
     [[
     x ↦ x
     ]]
 *)
Definition id : forall {A}, Func A A.
Proof.
  intros A.
  exact (by_formula (fun x => x)).
Defined.

(**
     Again, [id_ok] is a simple corollary of [by_formula_ok]. Ignore
     the weird syntax of its statement. It is needed for minor
     technical reasons.
 *)
Corollary id_ok : forall {A : Type} x, app (@id A) x = x.
Proof.
  intros A x.
  unfold id.
  rewrite by_formula_ok.
  reflexivity.
Qed.

(**
     The identity function is the "multiplicative identity" with respect
     to composition.
 *)
Theorem id_left : forall {dom cod} (f : Func dom cod), comp f id = f.
Proof.
  intros dom cod f.
  apply funext.
  intros x.
  rewrite comp_ok.
  rewrite id_ok.
  reflexivity.
Qed.

Theorem id_right : forall {dom cod} (f : Func dom cod), comp id f = f.
Proof.
  intros dom cod f.
  apply funext.
  intros x.
  rewrite comp_ok.
  rewrite id_ok.
  reflexivity.
Qed.

(**
     A _surjective_ function is a function in which every element
     in the codomain is mapped by some element in the domain.
 *)
Definition surjective {dom cod} (f : Func dom cod) :=
  forall y : cod, exists x : dom, app f x = y.

(**
     An _injective_ function is a function in which no two elements in the
     domain are mapped to the same element in the codomain.
 *)
Definition injective {dom cod} (f : Func dom cod) :=
  forall x x' : dom, app f x = app f x' -> x = x'.

(**
     A trivial surjective function is the identity function.
 *)
Example id_sur : forall {A}, surjective (@id A).
Proof.
  intros A a.
  exists a.
  rewrite id_ok.
  reflexivity.
Qed.

(**
     A trivial injective function is the identity function.
 *)
Example id_inj : forall {A}, injective (@id A).
Proof.
  intros A a a' eq.
  rewrite id_ok in eq.
  rewrite id_ok in eq.
  exact eq.
Qed.

(**
     A function [f : dom -> cod] is invertible if there is a
     function [g : cod -> dom] so that [comp f g = id] and
     [comp g f = id].
 *)
Definition invertible {A B} (f : Func A B) :=
  exists g : Func B A, comp f g = id /\ comp g f = id.

(**
     Every bijection is invertible.
 *)
Theorem bij_then_inv :
  forall {A B} (f : Func A B), injective f -> surjective f -> invertible f.
Proof.
  intros A B f inj sur.
  unfold invertible.
  unfold surjective in sur.
  exists (by_formula (fun b => choice (sur b))).
  split.
  - apply funext.
    intros b.
    rewrite comp_ok.
    rewrite by_formula_ok.
    set (eq := choice_ok (sur b)).
    simpl in eq.
    rewrite eq.
    rewrite id_ok.
    reflexivity.
  - apply funext.
    intros a.
    rewrite comp_ok.
    rewrite by_formula_ok.
    set (eq := choice_ok (sur (app f a))).
    simpl in eq.
    unfold injective in inj.
    apply inj in eq.
    rewrite id_ok.
    exact eq.
Qed.

(**
     The composition of two invertible functions is invertible.
 *)
Theorem inv_closed_under_comp :
  forall {A B C} (g : Func B C) (f : Func A B),
    invertible g -> invertible f -> invertible (comp g f).
Proof.
  intros A B C g f [gi [eq_g1 eq_g2]] [fi [eq_f1 eq_f2]].
  exists (comp fi gi).
  split.
  - rewrite comp_assoc.
    pattern (comp (comp g f) fi).
    rewrite <- comp_assoc.
    rewrite eq_f1.
    rewrite id_left.
    rewrite eq_g1.
    reflexivity.
  - rewrite comp_assoc.
    pattern (comp (comp fi gi) g).
    rewrite <- comp_assoc.
    rewrite eq_g2.
    rewrite id_left.
    rewrite eq_f2.
    reflexivity.
Qed.

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


(******************************************************************************)


(** * Final exam review problems *)

(** Show that if the law of excluded middle holds then the
    law of double negation elimination also holds. *)
Theorem lem_then_dne :
  (forall P : Prop, (~ P \/ P)) ->
  (forall Q : Prop, ~ ~ Q -> Q).
Proof.
  intros h Q nnq.
  destruct (h Q) as [nq | q].
  - contradiction.
  - exact q.
Qed.

(** Show that [exists] commutes with [/\]. *)
Theorem exists_commutes_product : forall {A B : Type}
                           (P : A -> Prop)
                           (Q : B -> Prop),
    (exists a, P a) /\ (exists b, Q b) <-> exists a b, P a /\ Q b.
Proof.
  intros A B P Q.
  split.
  - intros [[a pa] [b qb]].
    exists a, b.
    split.
    + exact pa.
    + exact qb.
  - intros [a [b [pa qb]]].
    split.
    + exists a.
      exact pa.
    + exists b.
      exact qb.
Qed.

(** An endofunction [f : A -> A] is _idempotent_ if [f ∘ f = f].
 Show that every invertible idempotent is just the identity function. *)
Theorem inv_idem_id : forall {A : Type} (f : Func A A),
    invertible f ->
    comp f f = f ->
    f = id.
Proof.
  intros A f [g [eq1 eq2]] eq.
  assert (h : comp g (comp f f) = comp g f). {
    rewrite eq.
    reflexivity.
  }
  rewrite comp_assoc in h.
  rewrite eq2 in h.
  rewrite id_right in h.
  exact h.
Qed.

(** Consider the following definitions. *)
Definition tame n := exists k, n = 3 * k.
Definition moderate n := exists k, n = S (3 * k).
Definition wild n := exists k, n = S (S (3 * k)).

(** Show that every natural number is either tame, moderate, or wild. *)
Theorem tame_moderate_wild :
  forall n, tame n \/ moderate n \/ wild n.
Proof.
  induction n.
  - left.
    exists 0.
    reflexivity.
  - destruct IHn as [t | [m | w]].
    + right. left.
      destruct t as [x eq].
      exists x.
      rewrite eq.
      reflexivity.
    + right. right.
      destruct m as [x eq].
      exists x.
      rewrite eq.
      reflexivity.
    + left.
      destruct w as [x eq].
      unfold tame.
      rewrite eq.
      exists (S x).
      ring.
Qed.

Lemma helper1 : forall x, 1 <> 3 * x.
Proof.
  intros x eq.
  destruct x.
  - discriminate.
  - simpl in eq.
    assert (eq' : S (x + S (x + S (x + 0))) = S (S (S (x + x + x)))). {
      ring.
    }
    rewrite eq' in eq.
    discriminate.
Qed.

Lemma helper2 : forall x, 2 <> 3 * x.
Proof.
  intros x eq.
  destruct x.
  - discriminate.
  - simpl in eq.
    assert (eq' : S (x + S (x + S (x + 0))) = S (S (S (x + x + x)))). {
      ring.
    }
    rewrite eq' in eq.
    discriminate.
Qed.

(** Tameness and wildness can be equivalently expressed as follows.
 We'll ask you to prove a lemma that helps us prove this fact. *)
Inductive tame' : nat -> Prop :=
| tame_z : tame' 0
| tame_s : forall n, wild' n -> tame' (S n)
with wild' : nat -> Prop :=
| wild_s : forall n, tame' n -> wild' (S (S n)).

(** Prove that if [n] is tame then [S (S n)] satisfies [wild']. *)
Theorem tame_then_ss_wild' :
  forall n, tame n -> wild' (S (S n)).
Proof.
  induction n using strong_nat_ind.
  destruct n as [|[|[|]]].
  - intros _.
    apply wild_s.
    apply tame_z.
  - intros t.
    destruct t as [x eq].
    apply helper1 in eq.
    contradiction.
  - intros t.
    destruct t as [x eq].
    apply helper2 in eq.
    contradiction.
  - intros t.
    apply wild_s.
    apply tame_s.
    apply H.
    + repeat constructor.
    + destruct t as [x eq].
      unfold tame.
      destruct x.
      * discriminate.
      * simpl in eq.
        assert (eq' : S (x + S (x + S (x + 0))) = (S (S (S (3 * x))))). {
          ring.
        }
        rewrite eq' in eq.
        repeat apply Nat.succ_inj in eq.
        exists x.
        exact eq.
Qed.

(** [tame] and [tame'] are equivalent.
 This is not part of the practice exam. *)
Theorem tame_eqv_tame' :
  forall n, tame n <-> tame' n.
Proof.
  intros n.
  split.
  - intros t.
    apply tame_then_ss_wild' in t.
    inversion t.
    exact H0.
  - induction n using strong_nat_ind.
    intros t.
    destruct n as [|[|[|]]].
    + exists 0.
      reflexivity.
    + inversion t.
      inversion H1.
    + inversion t.
      inversion H1.
    + inversion t.
      inversion H1.
      subst.
      apply H in H3.
      * destruct H3 as [x eq].
        exists (S x).
        rewrite eq.
        ring.
      * repeat constructor.
Qed.
           
