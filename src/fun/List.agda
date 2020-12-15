module fun.List where

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

_++_ : ∀ { A : Set } → List A → List A → List A
_++_ [] ys = ys
_++_ (x ∷ xs) ys = x ∷ (xs ++ ys)
