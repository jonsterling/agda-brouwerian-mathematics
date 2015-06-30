{-# OPTIONS --type-in-type #-}

open import fibration

module neighborhoods (F : 𝔉 Set) where

  open import pervasives
  open import trees F
  open 𝔉 F

  data approximation : Set
  refinement : approximation → Set

  -- This is a generalization of the role that finite sequences (prefixes) play
  -- in Brouwer's spreads, bars, etc..
  data approximation where
    ⟨⟩ : approximation
    _⌢_ : (s : approximation) → (refinement s → dom) → approximation

  infixr 8 _⌢_

  refinement ⟨⟩ = Unit
  refinement (s ⌢ σ) = Σ[ p ∶ refinement s ] map (σ p)


  _⊕_ : approximation → approximation → approximation
  u ⊕ v = Σ.fst (compute u v)
    where
      mutual
        data R : approximation → approximation → approximation → Set where
          ⟨⟩ : ∀ {u} → R u ⟨⟩ u
          snoc : ∀ {u v u⊕v σ} (D : R u v u⊕v) → R u (v ⌢ σ) (u⊕v ⌢ σ ∘ str D)

        str : ∀ {u v u⊕v} → R u v u⊕v → refinement u⊕v → refinement v
        str ⟨⟩ _ = ⟨⟩
        str (snoc D) ⟨ r , m ⟩ = ⟨ _ , m ⟩

      compute : ∀ u v → Σ[ w ∶ approximation ] R u v w
      compute u ⟨⟩ = ⟨ _ , ⟨⟩ ⟩
      compute u (v ⌢ x) = ⟨ _ , snoc (Σ.snd (compute u v)) ⟩

  _♮ : 𝔉 Set
  _♮ = approximation ↓ refinement

  record path : Set where
    coinductive
    field
      head : dom
      tail : Σ[ p ∶ map head ] path

  prefix : path → ℕ → approximation
  prefix α ze = ⟨⟩
  prefix α (su n) = prefix (Σ.snd α.tail) n ⌢ (λ x → α.head)
    where
      module α = path α
