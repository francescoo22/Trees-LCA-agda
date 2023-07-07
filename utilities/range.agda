open import utilities.equality
open import utilities.natural

module utilities.range where

  --- x ∈ a ⋯ b : x ≥ a && x < b
  data _∈_⋯_ : ℕ → ℕ → ℕ → Set where
    base : {x a b : ℕ} → x ≥ a → x < b → x ∈ a ⋯ b

  lemma-eq-range : {x a b c : ℕ} → x ∈ a ⋯ b → b ≡ c → x ∈ a ⋯ c
  lemma-eq-range p refl = p

  lemma-singleton-range : {x a : ℕ} → x ∈ a ⋯ (succ a) → x ≡ a
  lemma-singleton-range (base x₁ x₂) = lemma-≥-<-to-≡ x₁ x₂

  lemma-split-range : {a b x : ℕ} → (c : ℕ) → x ∈ a ⋯ b → (x ∈ a ⋯ c) ⊎ (x ∈ c ⋯ b)
  lemma-split-range {x = x} c (base x≥a x<b) with lemma-split-inequalities x c
  ... | left x<c = left (base x≥a x<c)
  ... | right x≥c = right (base x≥c x<b)

  lemma-split-add-range : {n a b c : ℕ} → n ∈ a ⋯ (b + c) → (n ∈ a ⋯ b) ⊎ (n ∈ b ⋯ (b + c))
  lemma-split-add-range {n} {b = b} p with lemma-split-inequalities n b
  lemma-split-add-range {n} {b = b} (base x₁ x₂) | left x = left (base x₁ x)
  lemma-split-add-range {n} {b = b} (base x₁ x₂) | right x = right (base x x₂)