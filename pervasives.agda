module pervasives where

data Void : Set where

record Unit : Set where
  constructor tt

record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B fst

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

_×_ : (A B : Set) → Set
A × B = Σ[ _ ∶ A ] B
infixr 8 _×_

record IsEquivalenceRelation {A : Set} (R : A → A → Set) : Set where
  field
    refl : ∀ {M} → R M M
    sym : ∀ {M N} → R M N → R N M
    trans : ∀ {M N O} → R M N → R N O → R M O

data _==_ {A : Set} (M : A) : A → Set where
  refl : M == M


