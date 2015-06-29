{-# OPTIONS --type-in-type #-}

module trees where

open import container
open import fibration

module _ (C : container) where
  private
    module C = 𝔉 C

  record spread : Set where
    coinductive
    field
      head : C.dom
      subtrees : C.map head → spread

  record fan : Set where
    inductive
    field
      head : C.dom
      subtrees : C.map head → fan

  module notation where
    μ⟨_⟩ : Set
    μ⟨_⟩ = fan

    ν⟨_⟩ : Set
    ν⟨_⟩ = spread
