{-# OPTIONS --copatterns #-}

module reals where

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

module ℕ where
  data t : Set where
    ze : t
    su : t → t
  {-# BUILTIN NATURAL t #-}

  data _>_ : t → t → Set where
    >i : ∀ N → su N > N

  _+_ : t → t → t
  ze + N = N
  su M + N = su (M + N)

  _*_ : t → t → t
  ze * N = ze
  su M * N = N + (M * N)

module ℤ where
  data t : Set where
    -[1+_] : (n : ℕ.t) → t
    +_ : (n : ℕ.t) → t

  _⊖_ : ℕ.t → ℕ.t → t
  m ⊖ ℕ.ze = + m
  ℕ.ze ⊖ ℕ.su n = -[1+ n ]
  ℕ.su m ⊖ ℕ.su n = m ⊖ n

  -_ : t → t
  - (+ ℕ.su n) = -[1+ n ]
  - (+ ℕ.ze) = + ℕ.ze
  - -[1+ n ] = + ℕ.su n

  _+_ : t → t → t
  -[1+ m ] + -[1+ n ] = -[1+ ℕ.su (m ℕ.+ n) ]
  -[1+ m ] + + n = n ⊖ ℕ.su m
  + m + -[1+ n ] = m ⊖ ℕ.su n
  + m + + n = + (m ℕ.+ n)

  _-_ : t → t → t
  i - j = i + (- j)

  ∣_∣ : t → ℕ.t
  ∣ + n ∣ = n
  ∣ -[1+ n ] ∣ = ℕ.su n


  module Sign where
    data sign : Set where
      + - : sign

    _*_ : sign → sign → sign
    + * y = y
    - * + = -
    - * - = +

  _◃_ : Sign.sign → ℕ.t → t
  _ ◃ ℕ.ze = + ℕ.ze
  Sign.+ ◃ n = + n
  Sign.- ◃ ℕ.su n = -[1+ n ]

  sign : t → Sign.sign
  sign (+ _) = Sign.+
  sign -[1+ _ ] = Sign.-

  _*_ : t → t → t
  i * j = (sign i Sign.* sign j) ◃ (∣ i ∣ ℕ.* ∣ j ∣)

  _>_ : t → t → Set
  i > j with i - j
  i > j | -[1+ n ] = Void
  i > j | + ℕ.ze = Void
  i > j | + ℕ.su n = Unit

  record \0 : Set where
    constructor ⟨_,_⟩
    field
      val : t
      .nonzero : val == (+ 0) → Void

module ℚ where
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
  _-_ = {!!}

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

module ℝ where
  module CS = ChoiceSequence ℚ.t

  Cauchy : CS.t → Set
  Cauchy α =
    (e : ℚ.t)
      → e > ℚ0
      → Σ[ n ∶ ℕ.t ] ⟨ x ∈ α \\ n ⟩□ ∣ x - e ∣ ≤ e
    where
      open CS ; open ℚ
      ℚ0 = let open ℤ in ℚ.⟨ + 0 , \0.⟨ + 1 , (λ { () }) ⟩ ⟩

  t : Set
  t = Σ CS.t Cauchy


  module CS² = ChoiceSequence (ℚ.t × ℚ.t × ℤ.\0)

  _><_ : CS.t → CS.t → CS².t
  β >< γ = β >< γ [ `1 ]
    where
      `1 = ℤ.⟨ ℤ.+ 1 , (λ { () }) ⟩

      _><_[_] : CS.t → CS.t → ℤ.\0 → CS².t
      CS².t.head (β >< γ [ i ]) =
        ⟨ CS.t.head β , ⟨ CS.t.head γ , i ⟩ ⟩
      CS².t.tail (β >< γ [ ℤ.⟨ i , inz ⟩ ]) =
        CS.t.tail β >< CS.t.tail γ [ ℤ.⟨ i ℤ.+ (ℤ.+ 1) , admit ⟩ ]
          where
            postulate admit : _

  _~_ : t → t → Set
  ⟨ α , _ ⟩ ~ ⟨ β , _ ⟩ =
    ⟨ p ∈ α >< β ⟩□
      let
        ⟨ x , ⟨ y , n ⟩ ⟩ = p
      in
        ∣ x - y ∣ ≤ (`2 * (1/ n))

    where
      open CS² ; open Σ ; open ℚ

      `2 = ⟨ ℤ.+ 2 , ℤ.⟨ ℤ.+ 1 , (λ ()) ⟩ ⟩

      1/_ : ℤ.\0 → ℚ.t
      1/ i = ⟨ ℤ.+ 1 , i ⟩
