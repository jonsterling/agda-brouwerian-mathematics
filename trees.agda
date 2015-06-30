{-# OPTIONS --type-in-type #-}

open import fibration

module trees (F : 𝔉 Set) where
  open 𝔉 F

  record spread : Set where
    coinductive
    field
      head : dom
      subtrees : map head → spread

  record fan : Set where
    inductive
    constructor _∷_
    field
      head : dom
      subtrees : map head → fan

  module notation where
    μ⟨_⟩ : Set
    μ⟨_⟩ = fan

    ν⟨_⟩ : Set
    ν⟨_⟩ = spread
