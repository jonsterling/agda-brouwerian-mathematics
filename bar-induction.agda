{-# OPTIONS --type-in-type #-}

open import fibration

module bar-induction (F : 𝔉 Set) where
  open import pervasives
  open import neighborhoods using (_♮; _⌢_; ⟨⟩)
  open neighborhoods F hiding (_♮; _⌢_; ⟨⟩)
  open import trees
  open trees.notation

  private
    module F = 𝔉 F

  _bars_ : (B : approximation → Set) (s : approximation) → Set
  _bars_ B[_] s = μ⟨ U[_] ∶ (approximation → Set) ↓ B[ s ] + ((σ : refinement s → F.dom) → U[ s ⌢ σ ]) ⟩

  bar-induction-type : Set
  bar-induction-type =
    {A B : approximation → Set}
      → (∀ s → B s + (B s → Void)) -- B is a decidable bar
      → (∀ s → B s → A s)
      → (∀ s → (∀ σ → A (s ⌢ σ)) → A s) -- A is inductive
      → (u : approximation)
      → .(∀ α → Σ[ n ∶ ℕ ] B bars (u ⊕ prefix α n))
      → A (u ⊕ ⟨⟩)

  private
    postulate
      weaken-bar :
        (B : approximation → Set)
        {u : approximation}
        {σ : refinement u → F.dom}
        (α : path)
        (n : ℕ)
          → B bars (u ⊕ prefix α n)
          → B bars ((u ⌢ σ) ⊕ prefix α n)

  {-# NO_TERMINATION_CHECK #-}
  bar-induction : bar-induction-type
  bar-induction {B = B} B-dec B⊃A A-ind u is-bar with B-dec u
  ... | inl p = B⊃A u p
  ... | inr _ =
    A-ind u λ σ →
      bar-induction B-dec B⊃A A-ind (u ⌢ σ) λ α →
        let ⟨ n , bars ⟩ = is-bar α in
          ⟨ n , weaken-bar B α n bars ⟩
