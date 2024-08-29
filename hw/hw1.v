Section Homework1.

(**
   Instructions
   - Replace [Abort.] with [Qed.] after you successfully solve a problem.
   - If you can't solve a problem, comment out your code (if any) and
     end the problem with [Abort.] instead of [Qed.] In Coq, the
     syntax for comment is [(* comment goes here *)].
   - The number of submissions is unlimited.
   - Deadline: Feb 27 @ 23:55
 *)

Theorem contrap :
  forall (P Q : Prop), (P -> Q) -> ~ Q -> ~ P.
Proof.
Abort.

Theorem revcontrap :
  forall (P Q : Prop), (~ Q -> ~ P) -> P -> ~ ~ Q.
Proof.
Abort.

Theorem bothfalse :
  forall (P Q : Prop), ~ P -> ~ Q -> P <-> Q.
Proof.
Abort.

Theorem iff_trans :
  forall (P Q R : Prop), P <-> Q -> Q <-> R -> P <-> R.
Proof.
Abort.

Theorem or_uni :
  forall (P Q R : Prop), (P \/ Q -> R) <-> ((P -> R) /\ (Q -> R)).
Proof.
Abort.

End Homework1.
