{-# OPTIONS --type-in-type #-}

module fibration where

open import pervasives

infix 0 _↓_
record 𝔉 (I : Set) : Set₁ where
  constructor _↓_
  field
    dom : Set
    map : dom → I

make-fibration : ∀ {I : Set} (dom : Set) (map : dom → I) → 𝔉 I
make-fibration = _↓_

syntax make-fibration dom (λ s → map) = s ∶ dom ↓ map
