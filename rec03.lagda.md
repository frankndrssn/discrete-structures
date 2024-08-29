# Logical Equivalences

> :warning: you don't have to understand the code snippets.

```agda
{-# OPTIONS --safe #-}
module rec03 where
  open import prelude
  open import rec02
```

We say that two propositions, P and Q, are *logically equivalent*, denoted P ≡ Q, when (P ⇒ Q) ∧ (Q ⇒ P) is a tautology.

```agda
  data _≡_ : 𝐏 → 𝐏 → Type where
    Logical-Equivalence : {P : 𝐏} {Q : 𝐏} (prf : taut ((P ⇨ Q) ∧ (Q ⇨ P))) → P ≡ Q
  infix 26 _≡_
```
Logical equivalence is an *equivalence relation*, i.e.,
- (reflexive) P ≡ P for any proposition P;
- (symmetric) if P ≡ Q then Q ≡ P for any propositions P and Q;
- (transitive) if P ≡ Q and Q ≡ R then P ≡ R for any propositions P, Q, and R.

We will explore relations in more depth later.

```agda
  ≡-refl : {P : 𝐏} → P ≡ P
  ≡-refl = Logical-Equivalence (tautK λ 𝓜 → ≡-refl') where
    ≡-refl' : {b : 𝔹} → (if b then b) and (if b then b) ≐ true
    ≡-refl' {true} = ⋆
    ≡-refl' {false} = ⋆

  !_ : {P Q : 𝐏} → P ≡ Q → Q ≡ P
  ! Logical-Equivalence (tautK prf) = Logical-Equivalence (tautK (λ 𝓜 → ≡-symmetry' (prf 𝓜))) where
    ≡-symmetry' : {a b : 𝔹} → a iff b ≐ true → b iff a ≐ true
    ≡-symmetry' {true} {true} prf = ⋆
    ≡-symmetry' {false} {true} prf = prf
    ≡-symmetry' {false} {false} prf = prf

  _∙_ : {P Q R : 𝐏} → P ≡ Q → Q ≡ R → P ≡ R
  Logical-Equivalence (tautK prf) ∙ Logical-Equivalence (tautK prf') = Logical-Equivalence (tautK (λ 𝓜 → ≡-trans' (prf 𝓜) (prf' 𝓜))) where
    ≡-trans' : {a b c : 𝔹} → a iff b ≐ true → b iff c ≐ true → a iff c ≐ true
    ≡-trans' {true} {true} {true} prf prf' = ⋆
    ≡-trans' {false} {false} {false} prf prf' = ⋆

  ≡-¬ : {P Q : 𝐏} → P ≡ Q → ¬ P ≡ ¬ Q
  ≡-¬ (Logical-Equivalence (tautK prf)) = Logical-Equivalence (tautK (λ 𝓜 → ≡-¬' (prf 𝓜))) where
    ≡-¬' : {a b : 𝔹} → a iff b ≐ true → not a iff not b ≐ true
    ≡-¬' {true} {true} prf = ⋆
    ≡-¬' {true} {false} prf = prf
    ≡-¬' {false} {true} prf = prf
    ≡-¬' {false} {false} prf = ⋆

  ≡-∧ : {P Q R S : 𝐏} → P ≡ Q → R ≡ S → P ∧ R ≡ Q ∧ S
  ≡-∧ (Logical-Equivalence (tautK prf)) (Logical-Equivalence (tautK prf')) = Logical-Equivalence (tautK (λ 𝓜 → ≡-∧' (prf 𝓜) (prf' 𝓜))) where
    ≡-∧' : {a b c d : 𝔹} → a iff b ≐ true → c iff d ≐ true → a and c iff b and d ≐ true
    ≡-∧' {true} {true} {true} {true} prf prf' = ⋆
    ≡-∧' {true} {true} {false} {false} prf prf' = ⋆
    ≡-∧' {false} {false} {true} {true} prf prf' = ⋆
    ≡-∧' {false} {false} {false} {false} prf prf' = ⋆

  ≡-∨ : {P Q R S : 𝐏} → P ≡ Q → R ≡ S → P ∨ R ≡ Q ∨ S
  ≡-∨ (Logical-Equivalence (tautK prf)) (Logical-Equivalence (tautK prf')) = Logical-Equivalence (tautK (λ 𝓜 → ≡-∨' (prf 𝓜) (prf' 𝓜))) where
    ≡-∨' : {a b c d : 𝔹} → a iff b ≐ true → c iff d ≐ true → a or c iff b or d ≐ true
    ≡-∨' {true} {true} {true} {true} prf prf' = ⋆
    ≡-∨' {true} {true} {false} {false} prf prf' = ⋆
    ≡-∨' {false} {false} {true} {true} prf prf' = ⋆
    ≡-∨' {false} {false} {false} {false} prf prf' = ⋆

  ≡-⇨ : {P Q R S : 𝐏} → P ≡ Q → R ≡ S → P ⇨ R ≡ Q ⇨ S
  ≡-⇨ (Logical-Equivalence (tautK prf)) (Logical-Equivalence (tautK prf')) = Logical-Equivalence (tautK (λ 𝓜 → ≡-⇨' (prf 𝓜) (prf' 𝓜))) where
    ≡-⇨' : {a b c d : 𝔹} → a iff b ≐ true → c iff d ≐ true → (if a then c) iff (if b then d) ≐ true
    ≡-⇨' {true} {true} {true} {true} prf prf' = ⋆
    ≡-⇨' {true} {true} {false} {false} prf prf' = ⋆
    ≡-⇨' {false} {false} {true} {true} prf prf' = ⋆
    ≡-⇨' {false} {false} {false} {false} prf prf' = ⋆
  
  _≡⟨_⟩_ : (P : 𝐏) {Q R : 𝐏} → P ≡ Q → Q ≡ R → P ≡ R
  P ≡⟨ p ⟩ q = p ∙ q
  
  _∎ : (P : 𝐏) → P ≡ P
  P ∎ = ≡-refl

  infixr 0 _≡⟨_⟩_
  infix 1 _∎
```

## Truth Tables

Last time, we learnt how to show that a proposition is a tautology by appealing to the semantics, i.e., with a truth table.
We used this technique to show the following logical equivalences (and more).
- (conditional law) P ⇨ Q ≡ ¬ P ∨ Q
- (double negation law) ¬ (¬ P) ≡ P
- (∨ identity law) P ∨ ⊥ ≡ P
- (∨ commutative law) P ∨ Q ≡ Q ∨ P
- (∨ distributive law) P ∨ (Q ∧ R) ≡ (P ∨ Q) ∧ (P ∨ R)
- (∨ associative law) P ∨ (Q ∨ R) ≡ P ∨ Q ∨ R
- (∨ absorb law) P ∨ P ≡ P
- (∧ demorgan law) ¬ (P ∧ Q) ≡ ¬ P ∨ ¬ Q
- (∨ demorgan law) ¬ (P ∨ Q) ≡ ¬ P ∧ ¬ Q

```agda
  conditional-law : {P Q : 𝐏} → P ⇨ Q ≡ ¬ P ∨ Q
  conditional-law = Logical-Equivalence (tautK (λ 𝓜 → conditional-law')) where
    conditional-law' : {a b : 𝔹} → (if a then b) iff not a or b ≐ true
    conditional-law' {true} {true} = ⋆
    conditional-law' {true} {false} = ⋆
    conditional-law' {false} {true} = ⋆
    conditional-law' {false} {false} = ⋆

  double-negation-law : {P : 𝐏} → ¬ (¬ P) ≡ P
  double-negation-law = Logical-Equivalence (tautK (λ 𝓜 → double-negation-law')) where
    double-negation-law' : {b : 𝔹} → not (not b) iff b ≐ true
    double-negation-law' {true} = ⋆
    double-negation-law' {false} = ⋆

  ∨-identity-law : {P : 𝐏} → P ∨ ⊥ ≡ P
  ∨-identity-law = Logical-Equivalence (tautK λ 𝓜 → ∨-identity-law') where
    ∨-identity-law' : {b : 𝔹} → (b or false) iff b ≐ true
    ∨-identity-law' {true} = ⋆
    ∨-identity-law' {false} = ⋆

  ∨-commutative-law : {P Q : 𝐏} → P ∨ Q ≡ Q ∨ P
  ∨-commutative-law = Logical-Equivalence (tautK (λ 𝓜 → ∨-commutative-law')) where
    ∨-commutative-law' : {a b : 𝔹} → a or b iff b or a ≐ true
    ∨-commutative-law' {true} {true} = ⋆
    ∨-commutative-law' {true} {false} = ⋆
    ∨-commutative-law' {false} {true} = ⋆
    ∨-commutative-law' {false} {false} = ⋆

  ∨-distributive-law : {P Q R : 𝐏} → P ∨ (Q ∧ R) ≡ (P ∨ Q) ∧ (P ∨ R)
  ∨-distributive-law = Logical-Equivalence (tautK (λ 𝓜 → ∨-distributive-law')) where
    ∨-distributive-law' : {a b c : 𝔹} → a or (b and c) iff (a or b) and (a or c) ≐ true
    ∨-distributive-law' {true} {true} {true} = ⋆
    ∨-distributive-law' {true} {true} {false} = ⋆
    ∨-distributive-law' {true} {false} {true} = ⋆
    ∨-distributive-law' {true} {false} {false} = ⋆
    ∨-distributive-law' {false} {true} {true} = ⋆
    ∨-distributive-law' {false} {true} {false} = ⋆
    ∨-distributive-law' {false} {false} {true} = ⋆
    ∨-distributive-law' {false} {false} {false} = ⋆

  ∨-associative-law : {P Q R : 𝐏} → P ∨ (Q ∨ R) ≡ P ∨ Q ∨ R
  ∨-associative-law = Logical-Equivalence (tautK (λ 𝓜 → ∨-associative-law')) where
    ∨-associative-law' : {a b c : 𝔹} → a or (b or c) iff a or b or c ≐ true
    ∨-associative-law' {true} {true} {true} = ⋆
    ∨-associative-law' {true} {true} {false} = ⋆
    ∨-associative-law' {true} {false} {true} = ⋆
    ∨-associative-law' {true} {false} {false} = ⋆
    ∨-associative-law' {false} {true} {true} = ⋆
    ∨-associative-law' {false} {true} {false} = ⋆
    ∨-associative-law' {false} {false} {true} = ⋆
    ∨-associative-law' {false} {false} {false} = ⋆

  ∨-absorb-law : {P : 𝐏} → P ∨ P ≡ P
  ∨-absorb-law = Logical-Equivalence (tautK (λ 𝓜 → ∨-absorb-law')) where
    ∨-absorb-law' : {b : 𝔹} → b or b iff b ≐ true
    ∨-absorb-law' {true} = ⋆
    ∨-absorb-law' {false} = ⋆

  ∧-demorgan-law : {P Q : 𝐏} → ¬ (P ∧ Q) ≡ ¬ P ∨ ¬ Q
  ∧-demorgan-law = Logical-Equivalence (tautK (λ 𝓜 → ∧-demorgan-law')) where
    ∧-demorgan-law' : {a b : 𝔹} → not (a and b) iff not a or not b ≐ true
    ∧-demorgan-law' {true} {true} = ⋆
    ∧-demorgan-law' {true} {false} = ⋆
    ∧-demorgan-law' {false} {true} = ⋆
    ∧-demorgan-law' {false} {false} = ⋆

  ∨-demorgan-law : {P Q : 𝐏} → ¬ (P ∨ Q) ≡ ¬ P ∧ ¬ Q
  ∨-demorgan-law = Logical-Equivalence (tautK (λ 𝓜 → ∨-demorgan-law')) where
    ∨-demorgan-law' : {a b : 𝔹} → not (a or b) iff not a and not b ≐ true
    ∨-demorgan-law' {true} {true} = ⋆
    ∨-demorgan-law' {true} {false} = ⋆
    ∨-demorgan-law' {false} {true} = ⋆
    ∨-demorgan-law' {false} {false} = ⋆
```

## Syntactic Technique

Of course, truth table is not the only technique.
We can exploit the fact that logical equivalence is an equivalence relation to prove logical equivalences *syntactically*.

We start with a library of known logical equivalences.
These are
- (conditional-law) P ⇨ Q ≡ ¬ P ∨ Q
- (double-negation-law) ¬ (¬ P) ≡ P
- (∨-identity-law) P ∨ ⊥ ≡ P
- (∨-commutative-law) P ∨ Q ≡ Q ∨ P
- (∨-distributive-law) P ∨ (Q ∧ R) ≡ (P ∨ Q) ∧ (P ∨ R)
- (∨-associative-law) P ∨ (Q ∨ R) ≡ P ∨ Q ∨ R
- (∨-absorb-law) P ∨ P ≡ P
- (∧-demorgan-law) ¬ (P ∧ Q) ≡ ¬ P ∨ ¬ Q
- (∨-demorgan-law) ¬ (P ∨ Q) ≡ ¬ P ∧ ¬ Q

### ∧-identity-law

We can use these to prove new logical equivalences.
- P ∧ ⊤ ≡⟨ double-negation-law ⟩
- ¬ ¬ (P ∧ ⊤) ≡⟨ ∧-demorgan-law ⟩
- ¬ (¬ P ∨ ¬ ⊤) ≡⟨ trivial ⟩
- ¬ (¬ P ∨ ⊥) ≡⟨ ∨-identity-law ⟩
- ¬ (¬ P) ≡⟨ double-negation-law ⟩
- P ∎

Once a new logical equivalence has been proven, we can add it to the library of known logical equivalences.
The library now looks like this
- (conditional-law) P ⇨ Q ≡ ¬ P ∨ Q
- (double-negation-law) ¬ (¬ P) ≡ P
- (∨-identity-law) P ∨ ⊥ ≡ P
- (∨-commutative-law) P ∨ Q ≡ Q ∨ P
- (∨-distributive-law) P ∨ (Q ∧ R) ≡ (P ∨ Q) ∧ (P ∨ R)
- (∨-associative-law) P ∨ (Q ∨ R) ≡ P ∨ Q ∨ R
- (∨-absorb-law) P ∨ P ≡ P
- (∧-demorgan-law) ¬ (P ∧ Q) ≡ ¬ P ∨ ¬ Q
- (∨-demorgan-law) ¬ (P ∨ Q) ≡ ¬ P ∧ ¬ Q
- **(∧-identity-law) P ∧ ⊤ ≡ P**

```agda
  ∧-identity-law : {P : 𝐏} → P ∧ ⊤ ≡ P
  ∧-identity-law {P} = P ∧ ⊤ ≡⟨ ! double-negation-law ⟩
                       ¬ ¬ (P ∧ ⊤) ≡⟨ ≡-¬ ∧-demorgan-law ⟩
                       ¬ (¬ P ∨ ¬ ⊤) ≡⟨ ≡-¬ (≡-∨ ≡-refl (Logical-Equivalence (tautK (λ 𝓜 → ⋆)))) ⟩
                       ¬ (¬ P ∨ ⊥) ≡⟨ ≡-¬ ∨-identity-law ⟩
                       ¬ (¬ P) ≡⟨ double-negation-law ⟩
                       P ∎
```

### ∧-commutative-law

- P ∧ Q ≡⟨ double-negation-law ⟩
- ¬ ¬ (P ∧ Q) ≡⟨ ∧-demorgan-law ⟩
- ¬ (¬ P ∨ ¬ Q) ≡⟨ ∨-commutative-law ⟩
- ¬ (¬ Q ∨ ¬ P) ≡⟨ ∨-demorgan-law ⟩
- ¬ ¬ Q ∧ ¬ ¬ P ≡⟨ double-negation-law ⟩
- Q ∧ P ∎

```agda
  ∧-commutative-law : {P Q : 𝐏} → P ∧ Q ≡ Q ∧ P
  ∧-commutative-law {P} {Q} = P ∧ Q ≡⟨ ! double-negation-law ⟩
                              ¬ ¬ (P ∧ Q) ≡⟨ ≡-¬ ∧-demorgan-law ⟩
                              ¬ (¬ P ∨ ¬ Q) ≡⟨ ≡-¬ ∨-commutative-law ⟩
                              ¬ (¬ Q ∨ ¬ P) ≡⟨ ∨-demorgan-law ⟩
                              ¬ ¬ Q ∧ ¬ ¬ P ≡⟨ ≡-∧ double-negation-law double-negation-law ⟩
                              Q ∧ P ∎
```

### ∧-distributive-law

- P ∧ (Q ∨ R) ≡⟨ double-negation-law ⟩
- ¬ ¬ (P ∧ (Q ∨ R)) ≡⟨ ∧-demorgan-law ⟩
- ¬ (¬ P ∨ ¬ (Q ∨ R)) ≡⟨ ∨-demorgan-law ⟩
- ¬ (¬ P ∨ (¬ Q ∧ ¬ R)) ≡⟨ ∨-distributive-law ⟩
- ¬ ((¬ P ∨ ¬ Q) ∧ (¬ P ∨ ¬ R)) ≡⟨ ∧-demorgan-law ⟩
- ¬ (¬ P ∨ ¬ Q) ∨ ¬ (¬ P ∨ ¬ R) ≡⟨ ∨-demorgan-law ⟩
- (¬ ¬ P ∧ ¬ ¬ Q) ∨ (¬ ¬ P ∧ ¬ ¬ R) ≡⟨ double-negation-law ⟩
- (P ∧ Q) ∨ (P ∧ R) ∎

```agda
  ∧-distributive-law : {P Q R : 𝐏} → P ∧ (Q ∨ R) ≡ (P ∧ Q) ∨ (P ∧ R)
  ∧-distributive-law {P} {Q} {R} = P ∧ (Q ∨ R) ≡⟨ ! double-negation-law ⟩
                                   ¬ ¬ (P ∧ (Q ∨ R)) ≡⟨ ≡-¬ ∧-demorgan-law ⟩
                                   ¬ (¬ P ∨ ¬ (Q ∨ R)) ≡⟨ ≡-¬ (≡-∨ ≡-refl ∨-demorgan-law) ⟩
                                   ¬ (¬ P ∨ (¬ Q ∧ ¬ R)) ≡⟨ ≡-¬ ∨-distributive-law ⟩
                                   ¬ ((¬ P ∨ ¬ Q) ∧ (¬ P ∨ ¬ R)) ≡⟨ ∧-demorgan-law ⟩
                                   ¬ (¬ P ∨ ¬ Q) ∨ ¬ (¬ P ∨ ¬ R) ≡⟨ ≡-∨ ∨-demorgan-law ∨-demorgan-law ⟩
                                   (¬ ¬ P ∧ ¬ ¬ Q) ∨ (¬ ¬ P ∧ ¬ ¬ R) ≡⟨ ≡-∨ (≡-∧ double-negation-law double-negation-law) (≡-∧ double-negation-law double-negation-law) ⟩
                                   (P ∧ Q) ∨ (P ∧ R) ∎
```

### contraposition-law

- P ⇨ Q ≡⟨ conditional-law ⟩
- ¬ P ∨ Q ≡⟨ double-negation-law ⟩
- ¬ P ∨ ¬ ¬ Q ≡⟨ ∨-commutative-law ⟩
- ¬ ¬ Q ∨ ¬ P ≡⟨ conditional-law ⟩
- ¬ Q ⇨ ¬ P ∎

```agda
  contraposition-law : {P Q : 𝐏} → P ⇨ Q ≡ ¬ Q ⇨ ¬ P
  contraposition-law {P} {Q} = P ⇨ Q ≡⟨ conditional-law ⟩
                               ¬ P ∨ Q ≡⟨ ≡-∨ (≡-refl) (! double-negation-law) ⟩
                               ¬ P ∨ ¬ ¬ Q ≡⟨ ∨-commutative-law ⟩
                               ¬ ¬ Q ∨ ¬ P ≡⟨ ! conditional-law ⟩
                               ¬ Q ⇨ ¬ P ∎
```

### negation-law

- P ⇨ ⊥ ≡⟨ conditional-law ⟩
- ¬ P ∨ ⊥ ≡⟨ ∨-identity-law ⟩
- ¬ P ∎

```agda
  negation-law : {P Q : 𝐏} → P ⇨ ⊥ ≡ ¬ P
  negation-law {P} {Q} = P ⇨ ⊥ ≡⟨ conditional-law ⟩
                         ¬ P ∨ ⊥ ≡⟨ ∨-identity-law ⟩
                         ¬ P ∎
```

### implication-r

- P ∧ Q ⇨ R ≡⟨ conditional-law ⟩
- ¬ (P ∧ Q) ∨ R ≡⟨ ∧-demorgan-law ⟩
- (¬ P ∨ ¬ Q) ∨ R ≡⟨ ∨-associative-law ⟩
- ¬ P ∨ (¬ Q ∨ R) ≡⟨ conditional-law ⟩
- P ⇨ (¬ Q ∨ R) ≡⟨ conditional-law ⟩
- P ⇨ (Q ⇨ R) ∎

```agda
  implication-r : {P Q R : 𝐏} → P ∧ Q ⇨ R ≡ P ⇨ (Q ⇨ R)
  implication-r {P} {Q} {R} = P ∧ Q ⇨ R ≡⟨ conditional-law ⟩
                              ¬ (P ∧ Q) ∨ R ≡⟨ ≡-∨ ∧-demorgan-law ≡-refl ⟩
                              (¬ P ∨ ¬ Q) ∨ R ≡⟨ ! ∨-associative-law ⟩
                              ¬ P ∨ (¬ Q ∨ R) ≡⟨ ! conditional-law ⟩
                              P ⇨ (¬ Q ∨ R) ≡⟨ ≡-⇨ ≡-refl (! conditional-law) ⟩
                              P ⇨ (Q ⇨ R) ∎
```

### conjunction-r

- (P ⇨ Q) ∧ (P ⇨ R) ≡⟨ conditional-law ⟩
- (¬ P ∨ Q) ∧ (¬ P ∨ R) ≡⟨ ∨-distributive-law ⟩
- ¬ P ∨ (Q ∧ R) ≡⟨ conditional-law ⟩
- P ⇨ (Q ∧ R) ∎

```agda
  conjunction-r : {P Q R : 𝐏} → (P ⇨ Q) ∧ (P ⇨ R) ≡ P ⇨ (Q ∧ R)
  conjunction-r {P} {Q} {R} = (P ⇨ Q) ∧ (P ⇨ R) ≡⟨ ≡-∧ conditional-law conditional-law ⟩
                              (¬ P ∨ Q) ∧ (¬ P ∨ R) ≡⟨ ! ∨-distributive-law ⟩
                              ¬ P ∨ (Q ∧ R) ≡⟨ ! conditional-law ⟩
                              P ⇨ (Q ∧ R) ∎
```

### disjunction-l

- (P ⇨ R) ∧ (Q ⇨ R) ≡⟨ conditional-law ⟩
- (¬ P ∨ R) ∧ (¬ Q ∨ R) ≡⟨ ∨-commutative-law ⟩
- (R ∨ ¬ P) ∧ (R ∨ ¬ Q) ≡⟨ ∨-distributive-law ⟩
- R ∨ (¬ P ∧ ¬ Q) ≡⟨ ∨-commutative-law ⟩
- (¬ P ∧ ¬ Q) ∨ R ≡⟨ ∨-demorgan-law ⟩
- ¬ (P ∨ Q) ∨ R ≡⟨ conditional-law ⟩
- (P ∨ Q) ⇨ R ∎

```agda
  disjunction-l : {P Q R : 𝐏} → (P ⇨ R) ∧ (Q ⇨ R) ≡ (P ∨ Q) ⇨ R
  disjunction-l {P} {Q} {R} = (P ⇨ R) ∧ (Q ⇨ R) ≡⟨ ≡-∧ conditional-law conditional-law ⟩
                              (¬ P ∨ R) ∧ (¬ Q ∨ R) ≡⟨ ≡-∧ ∨-commutative-law ∨-commutative-law ⟩
                              (R ∨ ¬ P) ∧ (R ∨ ¬ Q) ≡⟨ ! ∨-distributive-law ⟩
                              R ∨ (¬ P ∧ ¬ Q) ≡⟨ ∨-commutative-law ⟩
                              (¬ P ∧ ¬ Q) ∨ R ≡⟨ ≡-∨ (! ∨-demorgan-law) ≡-refl ⟩
                              ¬ (P ∨ Q) ∨ R ≡⟨ ! conditional-law ⟩
                              (P ∨ Q) ⇨ R ∎
```

### disjunction-r

- (P ⇨ Q) ∨ (P ⇨ R) ≡⟨ conditional-law ⟩
- (¬ P ∨ Q) ∨ (¬ P ∨ R) ≡⟨ ∨-associative-law ⟩
- ¬ P ∨ Q ∨ ¬ P ∨ R ≡⟨ ∨-associative-law ⟩
- ¬ P ∨ (Q ∨ ¬ P) ∨ R ≡⟨ ∨-commutative-law ⟩
- ¬ P ∨ (¬ P ∨ Q) ∨ R ≡⟨ ∨-associative-law ⟩
- ¬ P ∨ ¬ P ∨ Q ∨ R ≡⟨ ∨-absorb-law ⟩
- ¬ P ∨ Q ∨ R ≡⟨ ∨-associative-law ⟩
- ¬ P ∨ (Q ∨ R) ≡⟨ conditional-law ⟩
- P ⇨ (Q ∨ R) ∎

```agda
  disjunction-r : {P Q R : 𝐏} → (P ⇨ Q) ∨ (P ⇨ R) ≡ P ⇨ (Q ∨ R)
  disjunction-r {P} {Q} {R} = (P ⇨ Q) ∨ (P ⇨ R) ≡⟨ ≡-∨ conditional-law conditional-law ⟩
                              (¬ P ∨ Q) ∨ (¬ P ∨ R) ≡⟨ ∨-associative-law ⟩
                              ¬ P ∨ Q ∨ ¬ P ∨ R ≡⟨ ≡-∨ (! ∨-associative-law) ≡-refl ⟩
                              ¬ P ∨ (Q ∨ ¬ P) ∨ R ≡⟨ ≡-∨ (≡-∨ ≡-refl ∨-commutative-law) ≡-refl ⟩
                              ¬ P ∨ (¬ P ∨ Q) ∨ R ≡⟨ ≡-∨ ∨-associative-law ≡-refl ⟩
                              ¬ P ∨ ¬ P ∨ Q ∨ R ≡⟨ ≡-∨ (≡-∨ ∨-absorb-law ≡-refl) ≡-refl ⟩
                              ¬ P ∨ Q ∨ R ≡⟨ ! ∨-associative-law ⟩
                              ¬ P ∨ (Q ∨ R) ≡⟨ ! conditional-law ⟩
                              P ⇨ (Q ∨ R) ∎
```
