open import equality
open import natural

module range where

  --- x ∈ a ⋯ b : x ≥ a && x < b
  data _∈_⋯_ : ℕ → ℕ → ℕ → Set where
    base : {x a b : ℕ} → x ≥ a → x < b → x ∈ a ⋯ b

  -- lemma-eq-range : {x a b c : ℕ} → x ∈ a ⋯ b → b ≡ c → x ∈ a ⋯ c
  -- lemma-eq-range p refl = p

  lemma-singleton-range : (x a : ℕ) → x ∈ a ⋯ (succ a) → x ≡ a
  lemma-singleton-range x a (base x₁ x₂) = lemma-≥-<-to-≡ x₁ x₂

  lemma-union-range : {n a b c : ℕ} → n ∈ a ⋯ (b + c) → (n ∈ a ⋯ b) ⊎ (n ∈ b ⋯ (b + c))
  lemma-union-range {n} {b = b} p with lemma-split-inequalities n b
  lemma-union-range {n} {b = b} (base x₁ x₂) | left x = left (base x₁ x)
  lemma-union-range {n} {b = b} (base x₁ x₂) | right x = right (base x x₂)