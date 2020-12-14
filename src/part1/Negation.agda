module part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open import part1.Relations using (_<_; Trichotomy)
open import part1.Connectives using (→-distrib-⊎)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

open _<_

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s x) = <-irreflexive x

data Tri (m n : ℕ) : Set where

  forward :
      (m < n) × ¬ (n < m) × ¬ (m ≡ n)
      ---------
    → Tri m n

  flipped :
      n < m × ¬ (m < n) × ¬ (n ≡ m)
      ---------
    → Tri m n

  equal :
      m ≡ n × ¬ (m < n) × ¬ (n < m)
      ---------
    → Tri m n

open _≡_

suc-≡ : ∀ {m n : ℕ}
  → suc m ≡ suc n
    -------------
  → m ≡ n
suc-≡ suc≡ = cong (λ x → x ∸ 1) suc≡

proveTri : ∀ (m n : ℕ) → Tri m n
proveTri zero zero = equal (refl , (λ ()), (λ ()))
proveTri (suc m) zero = flipped ( z<s , (λ ()), (λ ()))
proveTri zero (suc n) = forward ( z<s , (λ ()), (λ ()))
proveTri (suc m) (suc n) with proveTri m n
... | forward (m<n , ¬n<m , ¬m≡n ) = forward ( s<s m<n , (λ{ (s<s n<m) → ¬n<m n<m }) , (λ x → ¬m≡n (suc-≡ x)))
... | flipped (n<m , ¬m<n , ¬n≡m) = flipped ( s<s n<m , (λ{ (s<s m<n) → ¬m<n m<n }) , (λ x → ¬n≡m (suc-≡ x)))
... | equal (m≡n , ¬m<n , ¬n<m) = equal ( cong suc m≡n , (λ{ (s<s m<n) → ¬m<n m<n }) , (λ{ (s<s n<m) → ¬n<m n<m }) )

deMorgan : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
deMorgan = →-distrib-⊎

-- I don't think this is possible because we only know that A AND B is impossible.
-- Individually A or B may be possible
-- reDeMorgan : ∀ {A B : Set} → ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- reDeMorgan = {!!}

¬⊎-implies-¬× : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
¬⊎-implies-¬× =
  λ{ (inj₁ ¬a) → λ x → ¬a (proj₁ x)
   ; (inj₂ ¬b) → λ x → ¬b (proj₂ x)
   }

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })
