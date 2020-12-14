module fun.Monoid where

record Semigroup {A : Set} : Set where
  field
    <> : A → A → A
    -- <>-assoc :
