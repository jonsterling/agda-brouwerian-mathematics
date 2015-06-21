module integers where

open import pervasives
import naturals as ℕ

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

