module fun.Monoid where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import fun.List using (List; []; _∷_; _++_)

record Semigroup (A : Set) : Set where
  field
    _∙_ : A → A → A
    ∙-assoc : ∀ ( x y z : A ) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

list-assoc : ∀ { A : Set} (x y z : List A) → ((x ++ y) ++ z) ≡ (x ++ (y ++ z))
list-assoc {A} [] y zs = refl
list-assoc {A} (x ∷ xs) ys zs = cong (_∷_ x) (list-assoc xs ys zs)

list-semigroup : ∀ {A : Set} → Semigroup (List A)
list-semigroup =
  record {
    _∙_     = (_++_)
  ; ∙-assoc = list-assoc
  }
