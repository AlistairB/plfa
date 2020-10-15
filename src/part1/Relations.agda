module part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

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

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n


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
