module rationals where

open import pervasives
import integers as ℤ
import naturals as ℕ

record t : Set where
  constructor ⟨_,_⟩
  field
    numerator : ℤ.t
    denominator : ℤ.\0

_~_ : t → t → Set
⟨ M1 , ℤ.⟨ N1 , _ ⟩ ⟩ ~ ⟨ M2 , ℤ.⟨ N2 , _ ⟩ ⟩ =
  (M1 * N2) == (M2 * N1)
  where
    open ℤ

_>_ : t → t → Set
⟨ M1 , ℤ.⟨ N1 , _ ⟩ ⟩ > ⟨ M2 , ℤ.⟨ N2 , _ ⟩ ⟩ = (M1 ℤ.* N2) ℤ.> (M2 ℤ.* N1)

_≤_ : t → t → Set
i ≤ j = i > j → Void

_-_ : t → t → t
_-_ = FIXME
  where
    postulate FIXME : _

_*_ : t → t → t
⟨ M1 , ℤ.⟨ N1 , nz1 ⟩ ⟩ * ⟨ M2 , ℤ.⟨ N2 , nz2 ⟩ ⟩ = ⟨ M1 ℤ.* M2 , ℤ.⟨ N1 ℤ.* N2 , admit ⟩ ⟩
  where
    postulate admit : _

∣_∣ : t → t
∣ ⟨ num , ℤ.⟨ denom , nonzero ⟩ ⟩ ∣ = ⟨ ℤ.+ ℤ.∣ num ∣ , ℤ.⟨ ℤ.+ ℤ.∣ denom ∣ , (λ q → nonzero (lemma denom q)) ⟩ ⟩
  where
    lemma : (x : ℤ.t) → (ℤ.+ ℤ.∣ x ∣) == ℤ.+ 0 → x == (ℤ.+ 0)
    lemma ℤ.-[1+ ℕ.ze ] ()
    lemma ℤ.-[1+ ℕ.su n ] ()
    lemma (ℤ.+ .0) refl = refl
