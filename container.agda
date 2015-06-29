{-# OPTIONS --type-in-type #-}

module container where

open import pervasives
open import fibration

container : Set
container = 𝔉 Set

make-container : (S : Set) (P : S → Set) → container
make-container S P = S ↓ P

syntax make-container S (λ s → P) = s ∶ S ◃ P
