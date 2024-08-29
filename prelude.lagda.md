```agda
{-# OPTIONS --safe #-}
module prelude where
  open import Agda.Builtin.List
  open import Agda.Builtin.Nat

  Type = Set

  data 𝟙 : Type where
    ⋆ : 𝟙

  data 𝟘 : Type where

  data 𝔹 : Type where
    true false : 𝔹

  _≐_ : 𝔹 → 𝔹 → Type
  true ≐ true = 𝟙
  true ≐ false = 𝟘
  false ≐ true = 𝟘
  false ≐ false = 𝟙
  infix 19 _≐_

  if_then_else_ : {C : Type} → 𝔹 → C → C → C
  if true then c₁ else c₂ = c₁
  if false then c₁ else c₂ = c₂
```
