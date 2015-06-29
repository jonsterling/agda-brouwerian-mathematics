{-# OPTIONS --type-in-type #-}

open import fibration

module bars (F : 𝔉 Set) where
  open import pervasives
  open import neighborhoods
  open import trees
  open trees.notation

  private
    module F = 𝔉 F
    module F♮ = 𝔉 (F ♮)

  _bars_ : (B : F♮.dom → Set) (s : F♮.dom) → Set
  _bars_ B[_] s = μ⟨ U ∶ (F♮.dom → Set) ↓ B[ s ] + ((σ : F♮.map s → F.dom) → B[ s ⌢ σ ]) ⟩
