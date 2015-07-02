{-# OPTIONS --type-in-type #-}

open import fibration

module trees (F : 𝔉 Set) where
  open 𝔉 F

  record spread : Set where
    coinductive
    field
      head : dom
      subtrees : map head → spread

  module notation where
    ν⟨_⟩ : Set
    ν⟨_⟩ = spread
