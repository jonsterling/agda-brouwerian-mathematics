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

  mutual
    data append : approximation → approximation → approximation → Set where
      ⟨⟩ : ∀ {u} → append u ⟨⟩ u
      snoc : ∀ {u v uv σ} (D : append u v uv) → append u (v ⌢ σ) (uv ⌢ σ ∘ strengthen-refinement D)

    strengthen-refinement : ∀ {u v uv} → append u v uv → refinement uv → refinement v
    strengthen-refinement ⟨⟩ _ = ⟨⟩
    strengthen-refinement (snoc D) ⟨ r , m ⟩ = ⟨ _ , m ⟩

  compute-append : (u v : approximation) → Σ[ w ∶ approximation ] append u v w
  compute-append u ⟨⟩ = ⟨ _ , ⟨⟩ ⟩
  compute-append u (v ⌢ x) = ⟨ _ , snoc (Σ.snd D) ⟩
    where
      D = compute-append u v

  _⊕_ : approximation → approximation → approximation
  u ⊕ v = Σ.fst (compute-append u v)

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
