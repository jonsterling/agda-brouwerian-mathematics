{-# OPTIONS --type-in-type #-}

module bars where

open import pervasives
open import neighborhoods
open import fibration
open import trees

module _ (F : 𝔉 Set) (let module F = 𝔉 F) (let module F♮ = 𝔉 (F ♮))where
  _bars_ : ∀ (B : F♮.dom → Set) (s : F♮.dom) → Set
  _bars_ B s = μ⟨ U ∶ (F♮.dom → Set) ↓ B s + ((σ : F♮.map s → F.dom) → B (s ⌢ σ)) ⟩
    where
      open trees.notation
