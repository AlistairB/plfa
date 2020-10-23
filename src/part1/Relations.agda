module part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm; +-identityʳ; +-suc)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

-- Give an example of a preorder that is not a partial order.

-- a loves b , b loves a however a != b

-- Give an example of a partial order that is not a total order.

-- um fits inside eg. https://eli.thegreenplace.net/2018/partial-and-total-orders/

-- The above proof omits cases where one argument is z≤n and one argument is s≤s. Why is it ok to omit them?

-- s≤s says both must be suc n however z≤n says one is zero, so the case is not feasible.

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

≤-trans : ∀ {m n p : ℕ}
    -----
    → m ≤ n
    → n ≤ p
    → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s (m≤n)) (s≤s (n≤p)) = s≤s (≤-trans m≤n n≤p)

≤-anti-sym : ∀ {m n : ℕ}
    -----
    → m ≤ n
    → n ≤ m
    → m ≡ n
≤-anti-sym z≤n z≤n = refl
≤-anti-sym (s≤s (m≤n)) (s≤s (n≤m)) = cong suc (≤-anti-sym m≤n n≤m)

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n       = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...             | forward m≤n = forward (s≤s m≤n)
...             | flipped n≤m = flipped (s≤s n≤m)

-- ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → (n + p) ≤ (n + q)
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → (m + p) ≤ (n + p)
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → (m + p) ≤ (n + q)
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → (n * p) ≤ (n * q)
*-monoʳ-≤ zero    p q p≤q  = z≤n
*-monoʳ-≤ (suc n) p q p≤q  = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

-- +-mono-≤ : ∀ (m n p q : ℕ)
--   → m ≤ n
--   → p ≤ q
--     -------------
--   → (m + p) ≤ (n + q)

-- +-mono-≤ : ∀ (m n p q : ℕ)
--   → p ≤ q
--   → (n * p) ≤ (n * q)
--     -------------
--   → (p + (n * p)) ≤ (q + (n * q))

  -- p ≤ q → (suc n * p) ≤ (suc n * q)
  -- p ≤ q → (p + n * p) ≤ (q + n * q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → (m * p) ≤ (n * p)
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p  = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → (m * p) ≤ (n * q)
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

<-trans : ∀ {m n p : ℕ}
    -----
    → m < n
    → n < p
    → m < p
<-trans z<s (s<s (n<p)) = z<s
<-trans (s<s (m<n)) (s<s (n<p)) = s<s (<-trans m<n n<p)

data Trichotomy (m n : ℕ) : Set where

  forward :
      m < n
      ---------
    → Trichotomy m n

  flipped :
      n < m
      ---------
    → Trichotomy m n

  equal :
      n ≡ m
      ---------
    → Trichotomy m n

+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
    -------------
  → (n + p) < (n + q)
+-monoʳ-< zero    p q p<q  =  p<q
+-monoʳ-< (suc n) p q p<q  =  s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → (m + p) < (n + p)
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p  = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → (m + p) < (n + q)
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤-iff-< : ∀ (m n : ℕ)
  → suc m ≤ n
    -------------
  → m < n
≤-iff-< zero (suc n) s≤n = z<s
≤-iff-< (suc m) (suc n) (s≤s s≤n) = s<s (≤-iff-< m n s≤n)

≤-iff-<' : ∀ (m n : ℕ)
  → m < n
    -------------
  → suc m ≤ n
≤-iff-<' zero (suc n) m<n = s≤s z≤n
≤-iff-<' (suc m) (suc n) (s<s m<n) = s≤s (≤-iff-<' m n m<n)

inv-s<s : ∀ {m n : ℕ} → suc m < suc n → m < n
inv-s<s (s<s m<n) = m<n

m<n-m≤n : ∀ {m n : ℕ} → m < n → m ≤ n
m<n-m≤n z<s = z≤n
m<n-m≤n (s<s m<n) = s≤s (m<n-m≤n m<n)

<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited {m} {n} {p} m<n n<p = ≤-iff-< m p (≤-trans pr1 pr2) where
  pr1 : suc m ≤ n
  pr1 = ≤-iff-<' m n m<n

  pr2 : n ≤ p
  pr2 = m<n-m≤n n<p


data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
    -----------
  → odd (m + n)
e+o≡o em (suc en) = {!!}
  --suc (+-suc (o+e≡o em en))

-- +-even-suc : ∀ (m n : ℕ) → even (m + suc n) ≡ even (suc (m + n))
-- +-even-suc zero n = refl
-- +-even-suc (suc om) n =
--   begin
--     suc (suc (m + suc n))
--   ≡⟨⟩
--     suc (m + suc n)
--   ≡⟨ cong suc (+-even-suc m n) ⟩
--     suc (suc m + n)
--   ∎

-- o+o≡e : ∀ {m n : ℕ}
--   → odd m
--   → odd n
--     -----------
--   → even (m + n)
-- o+o≡e m (suc en) = suc (o+e≡o m en)

-- o+o≡e : ∀ {m n : ℕ}
--   → odd m
--   → odd n
--     -----------
--   → even (m + n)
-- o+o≡e (suc zero) on = on
-- o+o≡e (suc em) on = suc
