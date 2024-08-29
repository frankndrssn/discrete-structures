(** Feb 15 in class examples 
 *)
Lemma test1: forall P Q R : Prop, (P -> (Q -> R)) -> (P -> Q) -> P -> R.
Proof.
  intros P Q R f g p.
  apply f.
  - exact p.
  - apply g.
    exact p.
Qed.
  
Lemma test4: forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros P Q [np nq] [p | q].
  - contradiction.
  - contradiction.
Qed.
  
Lemma test4b: forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q f.
  split.
  - intros p.
    apply f.
    left.
    exact p.
  - intros q.
    apply f.
    right.
    exact q.
Qed.
  
Lemma test5: forall P Q : Prop, P /\ (P \/ Q) <-> P.
Proof.
  intros P Q.
  split.
  - intros [p [_ | q]].
    + exact p.
    + exact p.
  - intros p.
    split.
    + exact p.
    + left.
      exact p.
Qed.
  
Lemma test6: forall P Q R : Prop, P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  intros P Q R.
  split.
  - intros [p [q | r]].
    + left.
      split.
      * exact p.
      * exact q.
    + right.
      split.
      * exact p.
      * exact r.
  - intros [[p q] | [p r]].
    + split.
      * exact p.
      * left.
        exact q.
    + split.
      * exact p.
      * right.
        exact r.
Qed.

Lemma test7 : forall P Q : Prop, (Q \/ P) /\ (~P -> Q) <-> (P \/ Q).
Proof.
  intros P Q.
  split.
  - intros [[q | p] f].
    + right.
      exact q.
    + left.
      exact p.
  - intros [p | q].
    + split.
      * right.
        exact p.
      * intros np.
        contradiction.
    + split.
      * left.
        exact q.
      * intros _.
        exact q.
Qed.

Lemma test8: forall P Q R : Prop, (P -> (Q /\ R)) -> ~Q -> ~P.
Proof.
  intros P Q R f nq p.
  apply f in p.
  destruct p as [q _].
  contradiction.
Qed.
  
Lemma test9 : forall P Q : Prop, (P -> P -> Q) -> P -> Q.
Proof.
  intros P Q f p.
  apply f.
  - exact p.
  - exact p.
Qed.
  
Lemma test10 : forall P Q R T : Prop, (Q -> R -> T) -> (P -> Q) -> P -> R -> T.
Proof.
  intros P Q R T f g p r.
  apply f.
  - apply g.
    exact p.
  - exact r.
Qed.
  
Lemma test11 : forall P Q R : Prop, (P -> Q -> R) -> (P -> Q) -> (P -> R).
Proof.
  intros P Q R f g p.
  apply f.
  - exact p.
  - apply g.
    exact p.
Qed.
  
Lemma test12 : forall P Q R : Prop, P -> Q -> (P -> Q -> R) -> R.
Proof.
  intros P Q R p q f.
  apply f.
  - exact p.
  - exact q.
Qed.
