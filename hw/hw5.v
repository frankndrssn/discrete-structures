Require Import ZArith.

(**
   Instructions
   - Replace [Abort.] with [Qed.] after you successfully solve a problem.
   - If you can't solve a problem, comment out your code (if any) and
     end the problem with [Abort.] instead of [Qed.] In Coq, the
     syntax for comment is [(* comment goes here *)].
   - The number of submissions is unlimited.
   - Deadline: Apr 25 @ 23:55
 *)

Open Scope Z_scope.

Theorem mod_mult_or :
  forall a b c : Z, (a | b) \/ (a | c) -> (a | b * c).
Proof.
Abort.

Theorem mod_mult :
  forall a b c : Z, (a | b) /\ (a | c) -> (a | b * c).
Proof.
Abort.
  
Close Scope Z_scope.
