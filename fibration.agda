module fibration where

open import pervasives

infix 0 _↓_
record 𝔉{ℓ₁ ℓ₂} (I : Set ℓ₁) : Set (ℓ₁ ⊔ lsuc ℓ₂) where
  constructor _↓_
  field
    dom : Set ℓ₂
    map : dom → I

make-fibration : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} (dom : Set ℓ₂) (map : dom → I) → 𝔉 I
make-fibration = _↓_

syntax make-fibration dom (λ s → map) = s ∶ dom ↓ map

𝔉Set : ∀ {ℓ} → Set (lsuc ℓ)
𝔉Set{ℓ} = 𝔉 {lsuc ℓ} {ℓ} (Set ℓ)
