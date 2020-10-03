module part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    -- the reduction to this is automatic, thus not actually required, but makes what is happening clearer
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎
  where
  +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
  +-assoc-1 n p =
    begin
      (1 + n) + p
    ≡⟨⟩
      suc (zero + n) + p
    ≡⟨⟩
      suc ((zero + n) + p)
    ≡⟨ cong suc (+-assoc-0 n p) ⟩
      suc (zero + (n + p))
    ≡⟨⟩
      1 + (n + p)
    ∎
    where
    +-assoc-0 : ∀ (n p : ℕ) → (zero + n) + p ≡ zero + (n + p)
    +-assoc-0 n p =
      begin
        (zero + n) + p
      ≡⟨⟩
        n + p
      ≡⟨⟩
        zero + (n + p)
      ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    (suc m) + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    (suc m)
  ∎

+-identityl : ∀ (m : ℕ) → zero + m ≡ m
+-identityl m = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n =
  begin
    (suc m) + (suc n)
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ (+-identityʳ m) ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ (+-suc m n) ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc n + m
  ∎

+-comm2 : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm2 zero n =
  begin
    zero + n
  ≡⟨⟩
    n
  ≡⟨ sym (+-identityʳ n) ⟩
    n + zero
  ∎
+-comm2 (suc m) n =
  begin
    suc m + n
  ≡⟨⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm2 m n) ⟩
    suc (n + m)
  ≡⟨ sym (+-suc n m) ⟩
    n + suc m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange zero n p q =
  begin
    (zero + n) + (p + q)
  ≡⟨⟩
    n + (p + q)
  ≡⟨ sym (+-assoc n p q) ⟩
    (n + p) + q
  ≡⟨⟩
    zero + (n + p) + q
  ∎
+-rearrange (suc m) n p q =
  begin
    (suc m + n) + (p + q)
  ≡⟨⟩
    suc (m + n) + (p + q)
  ≡⟨ cong suc (+-rearrange m n p q) ⟩
    suc m + (n + p) + q
  ∎

+-rearrange2 : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange2 m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ≡⟨⟩
    m + (n + p) + q
  ∎


-- +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- +-assoc′ zero n p = refl
-- +-assoc′ (suc m) n p = {!   !}

-- +-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
-- +-swap m n p =
--   begin
--     m + (n + p)
--   ≡⟨ +-comm m (n + p) ⟩
--     (n + p) + m
--   ≡⟨⟩
--     n + (m + p)
--   ∎

lemma : ∀ {a b c d : ℕ} → (a ≡ b) → (d + (a + c)) ≡ (d + (b + c))
lemma eq rewrite eq = refl

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl
