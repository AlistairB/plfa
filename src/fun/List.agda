module fun.List where

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
