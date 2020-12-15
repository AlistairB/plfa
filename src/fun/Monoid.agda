module fun.Monoid where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

record Semigroup {A : Set} : Set where
  field
    _∙_ : A → A → A
    ∙-assoc : ∀ ( x y z : A ) → ((x ∙ y) ∙ z) ≡ (x ∙ (y ∙ z))
