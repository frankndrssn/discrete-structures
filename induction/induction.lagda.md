```agda
{-# OPTIONS --safe #-}
open import Agda.Builtin.Nat hiding (_<_)
module induction where
```
We have seen how to implement the induction principle for ℕ.
```agda
  induction : {P : Nat → Set} → {- Set is unrelated to set theory we discussed in class. -}
              P 0 →
              ((k : Nat) → P k → P (suc k)) →
              (x : Nat) → P x
  {- If x = 0 then we are done because we have proved the base case. -}
  induction b f zero = b
  {- If x = suc y then we apply the induction step which says if we can prove P y then we can prove P (suc y). We can prove P y by making a recursive call: induction b f y -}
  induction b f (suc y) = f y (induction b f y)
```

We can generalize this argument to any data type equipped with a *well-founded* relation.
We need a few preliminary definitions:
Given a binary relation < (here, < is not necessarily the less-than relation), an element x is *accessible* if there is no infinite descending chain with respect to <, i.e, the element x eventually reaches a base case.
A binary relation is well-founded if every element is accessible, i.e., every element eventually reaches a base case.
```agda
  data acc {A : Set} (r : A → A → Set) : A → Set where
    acc_k : (x : A) → ((y : A) → r y x → acc r y) → acc r x

  wf : {A : Set} → (A → A → Set) → Set
  wf {A} r = (x : A) → acc r x
```

We can then define *well-founded induction* in terms of regular induction.
```agda
  wf-induction : {A : Set} →
                 {P : A → Set} →
                 (_<_ : A → A → Set) →
                 wf _<_ →
                 ((x : A) → ((y : A) → y < x → P y) → P x) →
                 (x : A) → P x
  wf-induction {A} {P}  _<_ wfp f x = h x (wfp x) where
    h : (x : A) → acc _<_ x → P x
    h x (acc .x k g) = f x (λ y l → h y (g y l))
```

Strong induction is a special case of well-founded induction because the less-than relation on ℕ is well-founded.
```agda
  data _<_ : Nat → Nat → Set where
    zero_suc : (n : Nat) → 0 < suc n
    n_suc : (n m : Nat) → n < m → n < suc m

  private
    <-0-acc : acc _<_ 0
    <-0-acc = acc 0 k (λ _ → h) where
      h : {y : Nat} → y < 0 → acc _<_ y
      h ()

    <-1-acc : acc _<_ 1
    <-1-acc = acc 1 k (λ _ → h) where
      h : {y : Nat} → y < 1 → acc _<_ y
      h (zero_suc .0) = <-0-acc

    <-suc-acc : (x : Nat) → acc _<_ x → acc _<_ (suc x)
    <-suc-acc zero _ = <-1-acc
    <-suc-acc (suc x) (acc .(suc x) k e) = acc (suc (suc x)) k h where
      h : (y : Nat) → y < suc (suc x) → acc _<_ y
      h zero l = <-0-acc
      h (suc y) (n .(suc y) suc .(suc x) l) = e (suc y) l

  <-wf : wf _<_
  <-wf zero = <-0-acc
  <-wf (suc x) = <-suc-acc x (<-wf x)

  strong-induction : {P : Nat → Set} →
                     ((x : Nat) → ((y : Nat) → y < x → P y) → P x) →
                     (x : Nat) → P x
  strong-induction = wf-induction _<_ <-wf
```
