Require Import ZArith.
Require Import Psatz.

Section NumberTheory.
  Open Scope Z_scope.

  (**
     In the induction module, we developed the [nat] data type
     and proved a number of theorems about this data type.
     We are going to extend [nat] with negative numbers,
     yielding the data type of integers [Z]. We are not
     going to develop this data type from scratch. Instead,
     we are going to develop an algorithm for the [Z] data
     type in this module.
   *)
  Print Z.

  (**
     A few relations on [Z] have already been defined.
     A particular relation that is of special interest
     in this module is the _divisibility relation_.
     An integer [n] _divides_ another integer [m] if
     [exists k, m = k * n]. This is usually written [(n | m)].
   *)
  Print Z.divide.
  (* Z.divide = fun x y : Z => exists z : Z, y = z * x
     : Z -> Z -> Prop *)

  (**
     Besides the [<=] relation on [Z], there are other
     sensible ways to order integers. As it turns out
     the divisibility relation on [Z] is a sensible
     notion of ordering on [Z]. We are going to use
     the divisibility relation heavily in this module.
   *)

  (**
     The _greatest common divisor_ of two integers
     [m] and [n] is an integer [k] so that
     - [(k | m)]
     - [(k | n)]
     - [k] is the "greatest" (with respect to the
       divisibility relation) with the two properties
       above, i.e., [forall k', (k' | m) -> (k' | n) -> (k' | k)].
     We can define the [is_gcd] relation as follows.
     [is_gcd k m n] means [k] is the gcd of [m] and [n].
   *)
  Inductive is_gcd (k : Z) : Z -> Z -> Prop :=
  | gcd_k : forall m n,
      (k | m) ->
      (k | n) ->
      (forall k', (k' | m) -> (k' | n) -> (k' | k)) ->
      is_gcd k m n.

  (**
     Facts about the [is_gcd] relation.
   *)
  Lemma is_gcd_sym :
    forall m n k, is_gcd k m n -> is_gcd k n m.
  Proof.
    intros m n k gcd.
    induction gcd.
    apply gcd_k.
    - exact H0.
    - exact H.
    - intros k' div1 div2.
      apply H1.
      + exact div2.
      + exact div1.
  Qed.

  Lemma is_gcd_mod' :
    forall a b k z : Z, is_gcd k (a - z * b) b -> is_gcd k a b.
  Proof.
    intros a b k z gcd.
    inversion gcd.
    constructor.
    - destruct H as [c eq].
      destruct H0 as [c' eq'].
      exists (c + z * c').
      nia.
    - exact H0.
    - intros k' div1 div2.
      apply H1.
      + apply Z.divide_sub_r.
        * exact div1.
        * apply Z.divide_mul_r.
          exact div2.
      + exact div2.
  Qed.
  
  Lemma is_gcd_mod :
    forall k a b, is_gcd k (a mod b) b -> is_gcd k a b.
  Proof.
    intros k a b gcd.
    set (eq := Z_div_mod_eq_full a b).
    assert (eq' : a mod b = a - (a / b) * b) by nia.
    rewrite eq' in gcd.
    apply is_gcd_mod' with (z := a / b).
    exact gcd.
  Qed.

  Lemma is_gcd_sign :
    forall k a b, is_gcd k (-a) b -> is_gcd k a b.
  Proof.
    intros k a b gcd.
    inversion gcd.
    apply gcd_k.
    - apply Znumtheory.Zdivide_opp_r_rev.
      exact H.
    - exact H0.
    - intros k' div1 div2.
      apply H1.
      + apply Znumtheory.Zdivide_opp_r.
        exact div1.
      + exact div2.
  Qed.

  Lemma is_gcd_sign2 :
    forall k a b, is_gcd k a b -> is_gcd (-k) a b.
  Proof.
    intros k a b gcd.
    inversion gcd.
    constructor.
    - destruct H as [c eq].
      exists (-c).
      subst.
      ring.
    - destruct H0 as [c eq].
      exists (-c).
      subst.
      ring.
    - intros k' div1 div2.
      apply H1 in div1.
      + destruct div1 as [c eq].
        exists (-c).
        subst.
        ring.
      + auto.
  Qed.

  Theorem is_gcd_zero_n :
    forall n, is_gcd n 0 n.
  Proof.
    intros n.
    apply gcd_k.
    - exists 0.
      simpl.
      reflexivity.
    - exists 1.
      symmetry.
      apply Z.mul_1_l.
    - intros k' _ div.
      exact div.
  Qed.
  
  (**
     Given two integers [a] and [b], we can compute a gcd of
     these two integers as follows: [is_gcd_zero_n] and
     [is_gcd_sym] tell us that if either [a] (resp., [b]) is
     [0], then [b] (resp., [a]) is a gcd of these two numbers.
     [is_gcd_mod] tells us how to reduce one of the arguments
     towards [0]. For example, here is one way to compute
     [gcd(10, 6)]:
     - [gcd(10, 6) = gcd(10 mod 6, 6) = gcd(4, 6) = gcd(6, 4)]
     - [gcd(6 mod 4, 4) = gcd(2, 4) = gcd(4, 2)]
     - [gcd(4, 2) = gcd(4 mod 2, 2) = gcd(0, 2) = 2]
   *)
  
  (**
     We can implement (a variant of) this algorithm in Coq.
     This is not a trivial algorithm so don't worry about it.
   *)
  Inductive gcd_sig (a b : Z) : Type :=
  | gcd_sig_k :
    forall u v,
      is_gcd (u * a + v * b) a b ->
      gcd_sig a b.
  
  Definition gcd_sig_comp' (a b : Z) :
    forall u3 v3 : Z,
      0 <= (u3 * a + v3 * b) ->
      forall u1 v1 u2 v2 : Z,
        u2 * a + v2 * b = u3 * a + v3 * b ->
        (forall k : Z, is_gcd k (u3 * a + v3 * b) (u1 * a + v1 * b)  ->
                  is_gcd k a b) ->
        gcd_sig a b.
  Proof.
    (* begin hide *)
    refine (fun u3 v3 le => _ le).
    set (m := u3 * a + v3 * b).
    pattern m.
    apply Z_lt_rec.
    - clear le m u3 v3.
      intros x f le u1 v1 u2 v2 eq g.
      destruct (Z_zerop x) as [eqz | neqz].
      + apply gcd_sig_k with (u := u1) (v := v1).
        apply g.
        rewrite eqz.
        apply is_gcd_zero_n.
      + assert (lt : 0 < x) by nia.
        clear le neqz.
        set (m := u1 * a + v1 * b) in *.
        set (q := m / x).
        set (r := m mod x).
        set (eq' := Z_div_mod_eq_full m x).
        fold q in eq'.
        fold r in eq'.
        assert (ieq : 0 <= r < x).
        {
          apply Z.mod_pos_bound.
          exact lt. 
        }
        clear lt.
        set (f' := f r ieq (proj1 ieq)).
        apply f' with (u1 := u2)
                      (v1 := v2)
                      (u2 := u1 - q * u2)
                      (v2 := v1 - q * v2).
        * nia.
        * rewrite eq.
          intros k gcd.
          apply g.
          apply is_gcd_sym.
          apply is_gcd_mod.
          exact gcd.
    - exact le.
      (* end hide *)
      (* some Coq magic... *)
  Defined.

  Definition gcd_sig_comp (a b : Z) : gcd_sig a b.
  Proof.
    destruct (Z_le_gt_dec 0 a) as [le | gt].
    - apply gcd_sig_comp' with (u3 := 1)
                               (v3 := 0)
                               (u1 := 0)
                               (v1 := 1)
                               (u2 := 1)
                               (v2 := 0).
      + nia.
      + reflexivity.
      + intros k gcd.
        assert (eq : 1 * a + 0 * b = a) by ring.
        assert (eq' : 0 * a + 1 * b = b) by ring.
        rewrite eq in gcd.
        rewrite eq' in gcd.
        exact gcd.
    - apply gcd_sig_comp' with (u3 := -1)
                               (v3 := 0)
                               (u1 := 0)
                               (v1 := 1)
                               (u2 := -1)
                               (v2 := 0).
      + nia.
      + reflexivity.
      + intros k gcd.
        apply is_gcd_sign.
        assert (eq : -1 * a + 0 * b = -a) by ring.
        assert (eq' : 0 * a + 1 * b = b) by ring.
        rewrite eq in gcd.
        rewrite eq' in gcd.
        exact gcd.
  Defined.

  Definition gcd (a b : Z) : Z :=
    match gcd_sig_comp a b with
    | gcd_sig_k _ _ u v _ => u * a + v * b
    end.

  Goal (gcd 1 3 = 1).
    unfold gcd.
    cbn.
    unfold gcd_sig_comp'; cbn.
    unfold Z_zerop.
  
  Close Scope Z_scope.
End NumberTheory.
