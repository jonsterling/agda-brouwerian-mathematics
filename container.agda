module container {ℓ} where

open import pervasives
open import fibration

container : Set (lsuc ℓ)
container = 𝔉 {lsuc ℓ} {ℓ} (Set ℓ)

make-container : (S : Set ℓ) (P : S → Set ℓ) → container
make-container S P = S ↓ P

syntax make-container S (λ s → P) = s ∶ S ◃ P
