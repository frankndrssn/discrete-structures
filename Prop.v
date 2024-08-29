Section Logic.
Variables (P Q R : Prop)
  (A : Type)
  (a b c : A)
  (S T : A -> Prop).
Let reset_point := I.

(**
   The proof system of first-order logic that we
   consider in this class has several
   _structural rules_. A notable one is the
   identity rule, which says if I have a hypothesis
   [p : P], then I can prove [P]. In Coq, we can
   use the [exact p] tactic, where [p] is the name
   of the hypothesis.
 *)
Reset reset_point.
Context (p : P).
Goal P.
Proof.
  exact p.
Qed.


(**
   The logical symbols of first-order logic (with equality)
   are [True], [False], [/\], [\/], [->], [forall], [exists], and [=]. The
   meanings of these symbols are determined by their
   _canonical proofs_ (introduction rules) and by
   their _canonical usage_ (elimination rules).
 *)

(** * [True] introduction
    The proposition [True] does not contain any useful
    information. It is self evident, so its canonical
    proof is trivial. Since it does not contain any
    useful information, it can't be used in any meaningful
    way, i.e., [True] does not have an elimination rule.
 *)
Reset reset_point.
Goal True.
Proof.
  trivial.
Qed.


(** * [False] elimination
    Dually, there is no canonical proof of the proposition [False].
    That is, [False] does not have an introduction rule.
    However, it has a very strong elimination rule: a false
    hypothesis entails anything.
 *)
Reset reset_point.
Context (false_hypothesis : False).
Goal P.
Proof.
  contradiction.
Qed.


(** * [/\] introduction
    [/\] is like a pair. If I have a proof [p] of [P] and a
    proof [q] of [Q], then I can construct a proof [(p, q)] of
    [P /\ Q]. In other words, to prove [P /\ Q], it suffices to
    prove [P] and [Q] separately. When the goal is of the
    form [P /\ Q], we can use the [split] tactic.
 *)
Reset reset_point.
Goal P /\ Q.
Proof.
  split.
  (* proof of [P] and [Q] *)
Abort.

(** * [/\] elimination
    Given a hypothesis [P /\ Q] we can extract a proof of [P]
    and a proof of [Q]. When there is a hypothesis [h : P /\ Q],
    we can use [destruct h as [p q]] to extract the two elements.
    Here, [p] and [q] can be any arbitrary fresh names.
 *)
Reset reset_point.
Context (h : P /\ Q).
Goal R.
Proof.
  destruct h as [p q].
  (* We now have a proof of [P] and a proof of [Q] in the context *)
Abort.


(** * [\/] introduction
    A proof of [P \/ Q] is either a proof of [P] or a
    proof of [Q]. If we want to prove [P], we can use
    [left]. For [Q], we can use [right].
 *)
Reset reset_point.
Goal P \/ Q.
Proof.
  left.
  (* proof of [P] *)
Abort.

Goal P \/ Q.
Proof.
  right.
  (* proof of [Q] *)
Abort.


(** * [\/] elimination
    Since [P \/ Q] consists of either a proof of [P] or
    a proof of [Q], Its canonical usage is case analysis.
    This is similar to the << if b then c1 else c2 >> construct
    in many programming languages: if << b >> is << true >> then do
    << c1 >> else do << c2 >>. Given a hypothesis [h : P \/ Q], we
    can use [destruct h as [p | q]] to do a case analysis on [h].
 *)
Reset reset_point.
Context (h : P \/ Q).
Goal R.
Proof.
  destruct h as [p | q].
  (* A proof of [R] assuming [P] *)
  (* and a proof of [R] assuming [Q] *)
Abort.


(** * [->] introduction
    [P -> Q] is like a function that takes a proof of [P]
    and outputs a proof of [Q]. The canonical way to prove
    [P -> Q] is to assume [P] and prove [Q]. We can use
    [intros p] to assume a new hypothesis [P]. Here,
    [p] can be any fresh name.
 *)
Reset reset_point.
Goal P -> Q.
Proof.
  intros p.
  (* Now, [P] is a hypothesis. *)
Abort.

(** * [->] elimination
    The canonical way to use a hypothesis [h : P -> Q] is
    modus ponens. It is (essentially) function application.
    We can use [apply f] to apply a function.
 *)
Reset reset_point.
Context (f : P -> Q).
Goal Q.
Proof.
  apply f.
  (* Now Coq demands us to provide an input to the function *)
Abort.

(* If there is a hypothesis [p : P], you can apply the function [f]
 to that hypothesis by [apply f in p]. *)
Context (p : P).
Goal Q.
  apply f in p.
  (* [p] is now the result of applying the function [f] *)
  exact p.
Qed.


(** * Negation [~]
   Negation is not a primitive connective in Coq. It is defined in terms
   of [->] and [False] as follows:
   [[
   ~P := P -> False
   ]]
   We can use the [unfold] tactic to unfold any (transparent) definition
   in the goal. If you want to unfold [~] in a hypothesis [h], you can use
   [unfold not in h].
 *)
Reset reset_point.
Goal ~ P.
Proof.
  unfold not.
Abort.

Context (h : ~ P).
Goal R.
Proof.
  unfold not in h.
Abort.

(* Alternatively, you can use [unfold "~"]. *)
Goal R.
Proof.
  unfold "~" in h.
Abort.


(** * If and only if [<->]
   In Coq, the connective [<->] is defined in terms of [->] and [/\]
   as follows:
   [[
   P <-> Q := (P -> Q) /\ (Q -> P)
   ]]
   We can use the [unfold] tactic to unfold its definition. We say
   that [P] and [Q] are _logically equivalent_ if [P <-> Q] holds.
 *)
Reset reset_point.
Goal P <-> Q.
Proof.
  unfold "<->".
Abort.

(* You can also use the [split] tactic directly since Coq
 knows the definition of "<->". *)
Goal P <-> Q.
Proof.
  split.
Abort.


(** * [forall] introduction
   [forall x : A, S x] is a function that takes [x] to a proof of [S x]
   ([x] has the property [S]). The [intros] tactic works.
   The variable [x] in [S x] is said to be _bound_ by [forall].
 *)
Reset reset_point.
Goal forall x : A, S x.
Proof.
  intros x.
  (* Proof of [S x] *)
Abort.

(** * [forall] elimination
    The canonical way to use a hypothesis [f : forall x : A, S x] is
    also function application.
 *)
Reset reset_point.
Context (f : forall x : A, S x).
Goal S a.
Proof.
  (* This time, Coq is smart enough to figure out what the input [x]
   should be *)
  apply f.
Qed.

(* You can also supply the input manually. There are
 two ways to accomplish this *)
Goal S a.
Proof.
  (* [f a] is Coq's syntax for applying the function [f] to
   the argument [a]. *)
  set (h := f a).
  exact h.
Qed.

Goal S a.
Proof.
  (* This tells Coq to apply the function [f] with argument [a] for
   the variable [x] *)
  apply f with (x := a).
Qed.


(** * [exists] introduction
    The canonical way to prove [exists x : A, S x] is to find an example
    with property [S]. We can use the [exists a] tactic to instantiate
    an example. The variable [x] in [S x] is said to be _bound_ by
    [exists].
 *)
Reset reset_point.
Goal exists x : A, S x.
Proof.
  exists a.
  (* Proof of [S a] *)
Abort.


(** * [exists] elimination
    Given a hypothesis [h : exists x : A, S x], we can extract an
    element [a'] of [A] that we know nothing about other than
    the fact that [S a'] holds. We can use [destruct h as [a' prf]]
    to do the extraction, where [a'] and [prf] can be any arbitrary
    fresh names.
 *)
Reset reset_point.
Context (h : exists x : A, S x).
Goal R.
Proof.
  destruct h as [a' prf].
(* Now, we have an element [a'] of [A] such that
   [S a'] holds. *)
Abort.


(** * [=] introduction
    The canonical way to prove [a = a] is [reflexivity].
    This requires the left-hand side and the right-hand
    side to be literally the same.
 *)
Reset reset_point.
Goal a = a.
Proof.
  reflexivity.
Qed.

(* If the goal (or a hypothesis) can be simplified,
 use the [simpl] (or [simpl in h]) tactic. *)
Goal 1 + 1 = 2.
Proof.
  simpl.
  reflexivity.
Qed.

(** * [=] elimination
    The canonical way to use a hypothesis [h : a = b] is
    rewriting. We can [rewrite h] to replace all
    free (not bound) occurrences of [a] in the goal with [b].
    We can also use [rewrite <- h] to replace all free occurrences
    of [b] with [a].
 *)
Context (h : a = b).
Goal b = a.
Proof.
  rewrite h.
  reflexivity.
Qed.

Goal b = a.
Proof.
  rewrite <- h.
  reflexivity.
Qed.

(* We can also [rewrite] in some other hypothesis [h'] *)
Context (h' : b = c).
Goal a = c.
Proof.
  rewrite <- h in h'.
  exact h'.
Qed.

(** * Homework problems
 *)
Reset reset_point.
Theorem curry : ((P /\ Q) -> R) -> (P -> (Q -> R)).
Proof.
Abort.

Theorem uncurry : (P -> (Q -> R)) -> ((P /\ Q) -> R).
Proof.
Abort.

Theorem or_uni : ((P \/ Q) -> R) <-> ((P -> R) /\ (Q -> R)).
Proof.
Abort.

Theorem and_uni : (P -> (Q /\ R)) <-> ((P -> Q) /\ (P -> R)).
Proof.
Abort.

Theorem lem_nonrefutable : ~ (~ (P \/ ~ P)).
Proof.
Abort.

Theorem eq_symmetric : a = b -> b = a.
Proof.
Abort.

Theorem eq_transitive : a = b -> b = c -> a = c.
Proof.
Abort.

Theorem ex_dist_and :
  (exists x : A, S x /\ T x) -> (exists x : A, S x) /\ (exists x : A, T x).
Proof.
Abort.

Theorem ex_dist_or :
  (exists x : A, S x \/ T x) -> (exists x : A, S x) \/ (exists x : A, T x).
Proof.
Abort.

(* Hint: the [set] tactic may be useful. *)
Theorem fa_dist_and :
  (forall x : A, S x /\ T x) <-> (forall x : A, S x) /\ (forall x : A, T x).
Proof.
Abort.

Theorem fa_dist_or :
  (forall x : A, S x) \/ (forall x : A, T x) -> (forall x : A, S x \/ T x).
Proof.
Abort.

Theorem fa_dist_imp :
  (forall x : A, S x -> T x) -> ((forall x : A, S x) -> (forall x : A, T x)).
Proof.
Abort.

Theorem ex_then_not_fa_not :
  (exists x : A, S x) -> (~ (forall x : A, ~ S x)).
Proof.
Abort.

End Logic.
