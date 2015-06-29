{-# OPTIONS --type-in-type #-}

module neighborhoods where

open import pervasives
open import fibration
open import container
open import trees

module _ (F : 𝔉 Set) where
  private
    module F = 𝔉 F

  mutual
    data approximation : Set₁ where
      ∇ : approximation
      _⌢_ : (s : approximation) → (refinement s → F.dom) → approximation
    infixr 8 _⌢_

    refinement : approximation → Set
    refinement ∇ = Unit
    refinement (s ⌢ σ) = Σ[ p ∶ refinement s ] F.map (σ p)

  _♮ : 𝔉 Set
  _♮ = approximation ↓ refinement

