module bars{ℓ} where

open import pervasives
open import neighborhoods{ℓ}
open import fibration
open import trees

module _ (F : 𝔉Set{ℓ}) (let module F = 𝔉 F) (let module F♮ = 𝔉 (F ♮))where
  _bars_ : ∀ (B : F♮.dom → Set (lsuc ℓ)) (s : F♮.dom) → Set (lsuc ℓ)
  _bars_ B s = μ⟨ U ∶ (F♮.dom → Set ℓ) ↓ B s + ((σ : F♮.map s → F.dom) → B (s ⌢ σ)) ⟩
    where
      open trees.notation
