Section Homework2.

(**
   Instructions
   - Replace [Abort.] with [Qed.] when you successfully solve a problem.
   - If you can't solve a problem, comment out your code (if any) and
     end the problem with [Abort.] instead of [Qed.] In Coq, the
     syntax for comment is [(* comment goes here *)].
   - The number of submissions is unlimited.
   - Deadline: Mar 7 @ 23:55
 *)

Theorem demorgan_exists :
  forall (A : Set) (P : A -> Prop), (exists x : A, ~ ~ P x) -> ~ forall x : A, ~ P x.
Proof.
Abort.

Theorem frobenius :
  forall (A : Set) (P : A -> Prop) (Q : Prop), (exists x : A, Q /\ P x) <-> Q /\ exists x : A, P x.
Proof.
Abort.

Theorem hodges :
  forall (A : Set) (R : A -> A -> Prop),
    (forall x : A, exists y : A, ~ R x y)
    -> ~ exists x : A, forall y : A, R x y.
Proof.
Abort.
  
End Homework2.
