module part1.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl  =  refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

≤-trans : ∀ {m n p : ℕ}
    -----
    → m ≤ n
    → n ≤ p
    → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s (m≤n)) (s≤s (n≤p)) = s≤s (≤-trans m≤n n≤p)

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

module ≤-Reasoning where

  infix  1 begin≤_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _≤∎

  begin≤_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  begin≤ x≤y  =  x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ x≤y  =  x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z  =  ≤-trans x≤y y≤z

  _≤∎ : ∀ (x : ℕ)
      -----
    → x ≤ x
  x ≤∎  =  ≤-refl

open ≤-Reasoning

-- cong≤ : ∀ (f : ℕ → ℕ) {m n : ℕ}
--   → m ≤ n
--     ---------
--   → f m ≤ f n
-- cong≤ f m≤n = {!!}

-- cong≤ : ∀ (f : ℕ → ℕ) {m n : ℕ}
--   → m ≤ n
--     ---------
--   → f m ≤ f n
-- cong≤ f {zero} {n} z≤n = {!!}
-- cong≤ f {suc m} {n} (s≤s m≤n) = {!!}

-- cong≤ : ∀ (f : ℕ → ℕ) {m n : ℕ}
--   → m ≤ n
--     ---------
--   → f m ≤ f n
-- cong≤ f {m} {n} m≤n with f m ≤ f n
--   |

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → (n + p) ≤ (n + q)
+-monoʳ-≤ zero    p q p≤q  =
  begin≤
    zero + p
  ≤⟨⟩
    p
  ≤⟨ p≤q ⟩
    q
  ≤⟨⟩
    zero + q
  ≤∎
+-monoʳ-≤ (suc n) p q p≤q  =
  begin≤
    suc n + p
  ≤⟨⟩
    suc (n + p)
  ≤⟨ cong≤ suc (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≤⟨⟩
    suc n + q
  ≤∎

  -- begin≤
  --   zero + p
  -- ≤⟨⟩
  --   p
  -- ≤⟨ p≤q ⟩
  --   q
  -- ≤⟨⟩
  --   zero + q
  -- ≤∎

-- p≤q
-- s≤s (+-monoʳ-≤ n p q p≤q)
