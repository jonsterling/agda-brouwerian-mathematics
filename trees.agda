module trees {ℓ} where

open import container{ℓ}
open import fibration

module _ (C : container) where
  private
    module C = 𝔉 C

  record spread : Set ℓ where
    coinductive
    field
      head : C.dom
      subtrees : C.map head → spread

  record fan : Set ℓ where
    inductive
    field
      head : C.dom
      subtrees : C.map head → fan

  module notation where
    μ⟨_⟩ : Set ℓ
    μ⟨_⟩ = fan

    ν⟨_⟩ : Set ℓ
    ν⟨_⟩ = spread
