module part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂;  _,_) -- renaming (_,_ to (_,_))
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import part1.Isomorphism using (_≃_; extensionality)
open import part1.Connectives using (→-distrib-×; η-×; case-⊎)
open import Function using (_∘_)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
      { to      = λ{ f → ( proj₁ ∘ f , proj₂ ∘ f ) }
      ; from    = λ{ ( g , h ) → λ x → ( g x , h x ) }
      ; from∘to = λ{ f → refl }
      ; to∘from = λ{ ( g , h ) → refl }
      }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ fb⊎fc = λ x → case-⊎ (λ y → inj₁ (y x)) (λ z → inj₂ (z x)) fb⊎fc

-- the converse does not stand as `∀ (x : A) → B x ⊎ C x` may return B or C for different x.
-- Thus you cannot get a function that always returns B or C

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- postulate
--   extensionality : ∀ {A B : Set} {f g : A → B}
--     → (∀ (x : A) → f x ≡ g x)
--       -----------------------
--     → f ≡ g

triIndexed : ∀ { B : Tri → Set } → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
triIndexed {B} =
  record
    { to      = λ f → ( f aa , f bb , f cc )
    ; from    =
        λ ( a , b , c ) →
          λ{ aa → a
          ; bb → b
          ; cc → c
          }
    ; from∘to = λ f → ∀-extensionality λ{ aa → refl ; bb → refl ; cc → refl }
    ; to∘from = λ y → refl
    }

-- η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
-- η-× ⟨ x , y ⟩ = refl
