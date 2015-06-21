module choice_sequence where

import naturals as ℕ

module ChoiceSequence (A : Set) where
  record t : Set where
    coinductive
    constructor _∷_
    field
      head : A
      tail : t

  record Everywhere (P : A → Set) (α : t) : Set where
    coinductive
    constructor _∷_
    module α = t α
    field
      head : P α.head
      tail : Everywhere P α

  syntax Everywhere (λ x → P) α = ⟨ x ∈ α ⟩□ P

  -- Cut off a finite prefix of a choice sequence
  _\\_ : t → ℕ.t → t
  α \\ ℕ.ze = α
  α \\ ℕ.su n = t.tail α \\ n

