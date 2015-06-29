{-# OPTIONS --type-in-type #-}

open import fibration

module neighborhoods (F : 𝔉 Set) where

  open import pervasives
  open 𝔉 F

  data approximation : Set
  refinement : approximation → Set

  data approximation where
    ∇ : approximation
    _⌢_ : (s : approximation) → (refinement s → dom) → approximation

  infixr 8 _⌢_

  refinement ∇ = Unit
  refinement (s ⌢ σ) = Σ[ p ∶ refinement s ] map (σ p)

  _♮ : 𝔉 Set
  _♮ = approximation ↓ refinement
