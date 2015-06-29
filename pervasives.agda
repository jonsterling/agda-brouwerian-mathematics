module pervasives where

open import Agda.Primitive using (lzero; lsuc; _⊔_) public

infixr 9 _∘_
_∘_ : ∀ {a b c}
  → {A : Set a}
  → {B : A → Set b}
  → {C : {x : A} → B x → Set c}
  → (g : (∀ {x} (y : B x) → C y))
  → (f : (x : A) → B x)
  → ((x : A) → C (f x))
g ∘ f = λ x → g (f x)

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const a b = a

data Void{ℓ} : Set ℓ where

record Unit{ℓ} : Set ℓ where
  constructor ⟨⟩

data _+_ {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  inl : A → A + B
  inr : B → A + B

data Bool : Set where
  tt ff : Bool

So : Bool → Set
So tt = Unit
So ff = Void

absurd : ∀ {i} {j} {A : Set i} → Void{j} → A
absurd ()

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B fst

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

_×_ : ∀ {i j} → (A : Set i) (B : Set j) → Set (i ⊔ j)
A × B = Σ[ _ ∶ A ] B
infixr 8 _×_

data _==_ {ℓ} {A : Set ℓ} (M : A) : A → Set ℓ where
  refl : M == M

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}


infix 1000 ♯_

postulate
  ∞_  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞_ #-}
{-# BUILTIN SHARP ♯_ #-}
{-# BUILTIN FLAT ♭ #-}

data ℕ{ℓ} : Set ℓ where
  ze : ℕ
  su : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
