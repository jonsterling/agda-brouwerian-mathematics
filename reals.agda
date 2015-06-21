{-# OPTIONS --copatterns #-}

module reals where

open import pervasives
import naturals as ℕ
import integers as ℤ
import rationals as ℚ
open import choice_sequence

module CS = ChoiceSequence ℚ.t

t : Set
t = Σ CS.t Cauchy
  where
    Cauchy : CS.t → Set
    Cauchy α =
      (e : ℚ.t)
        → e > `0
        → Σ[ n ∶ ℕ.t ] ⟨ x ∈ α \\ n ⟩□ ∣ x - e ∣ ≤ e
      where
        open CS ; open ℚ
        `0 = let open ℤ in ℚ.⟨ + 0 , \0.⟨ + 1 , (λ { () }) ⟩ ⟩

_~_ : t → t → Set
⟨ α , _ ⟩ ~ ⟨ β , _ ⟩ =
  ⟨ p ∈ α >< β ⟩□
    let
      ⟨ x , ⟨ y , n ⟩ ⟩ = p
    in
      ∣ x - y ∣ ≤ (`2 * (1/ n))

  where
    module CS² = ChoiceSequence (ℚ.t × ℚ.t × ℤ.\0)

    _><_ : CS.t → CS.t → CS².t
    β >< γ = β >< γ [ `1 ]
      where
        `1 = ℤ.⟨ ℤ.+ 1 , (λ { () }) ⟩

        open CS.t
        _><_[_] : CS.t → CS.t → ℤ.\0 → CS².t
        CS².t.head (β >< γ [ i ]) =
          ⟨ head β , ⟨ head γ , i ⟩ ⟩
        CS².t.tail (β >< γ [ ℤ.⟨ i , inz ⟩ ]) =
          tail β >< tail γ [ ℤ.⟨ i ℤ.+ (ℤ.+ 1) , admit ⟩ ]
            where
              postulate admit : _

    open CS² ; open Σ ; open ℚ

    `2 = ⟨ ℤ.+ 2 , ℤ.⟨ ℤ.+ 1 , (λ ()) ⟩ ⟩

    1/_ : ℤ.\0 → ℚ.t
    1/ i = ⟨ ℤ.+ 1 , i ⟩
