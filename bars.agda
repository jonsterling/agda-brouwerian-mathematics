{-# OPTIONS --type-in-type #-}

open import fibration

module bars (F : 𝔉 Set) where
  open import pervasives
  open import neighborhoods hiding (_⊕_; prefix; path)
  open import trees
  open trees.notation

  private
    module F = 𝔉 F
    module F♮ = 𝔉 (F ♮)

  _bars_ : (B : F♮.dom → Set) (s : F♮.dom) → Set
  _bars_ B[_] s = μ⟨ U ∶ (F♮.dom → Set) ↓ B[ s ] + ((σ : F♮.map s → F.dom) → B[ s ⌢ σ ]) ⟩


  open neighborhoods F using (_⊕_; prefix; path)

  bar-induction-type : Set
  bar-induction-type =
    {A B : F♮.dom → Set}
      → (∀ s → B s + (B s → Void)) -- B is a decidable bar
      → (∀ s → B s → A s)
      → (∀ s → (∀ σ → A (s ⌢ σ)) → A s) -- A is inductive
      → (u : F♮.dom)
      → .(∀ α → Σ[ n ∶ ℕ ] B bars (u ⊕ prefix α n))
      → A (u ⊕ ⟨⟩)

  strengthen-bar :
    (B : F♮.dom → Set)
    {u : F♮.dom}
    {σ : F♮.map u → F.dom}
    (α : path)
    (n : ℕ)
      → B bars (u ⊕ prefix α n)
      → B bars ((u ⌢ σ) ⊕ prefix α n)
  strengthen-bar B α n is-bar = admitted
    where
      postulate admitted : _
      -- TODO: prove this

  {-# NO_TERMINATION_CHECK #-}
  BI : bar-induction-type
  BI B-dec B⊃A A-ind u is-bar with B-dec u
  BI B-dec B⊃A A-ind u is-bar | inl p = B⊃A u p
  BI {B = B}B-dec B⊃A A-ind u is-bar | inr _ =
    A-ind u λ σ →
      BI B-dec B⊃A A-ind (u ⌢ σ) λ α →
        let ⟨ n , bars ⟩ = is-bar α in
          ⟨ n , strengthen-bar B α n bars ⟩
