module naturals where

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

