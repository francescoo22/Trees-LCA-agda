{-# OPTIONS --allow-unsolved-metas #-}
open import natural


module equality where
  infix 5 _≡_

  data _≡_ {X : Set} : X → X → Set where
    refl : {a : X} → a ≡ a


  infix 6 _⊎_
  
  data _⊎_ (A B : Set) : Set where
    left  : A → A ⊎ B
    right : B → A ⊎ B
    

  cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl


  symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
  symm refl = refl


  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  infix  3 _∎
  infixr 2 _≡⟨_⟩_ _≡⟨⟩_
  infix  1 begin_

  _≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = trans p q

  _≡⟨⟩_ : {A : Set} {y : A} → (x : A) → (q : x ≡ y) → x ≡ y
  x ≡⟨⟩ q = q

  _∎ : {A : Set} → (x : A) → x ≡ x
  x ∎ = refl

  begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
  begin p = p

  -------------------------
  --- additional lemmas ---
  -------------------------

  add-eq₁ : {a b c d : ℕ} → a ≡ b → c ≡ d → a + c ≡ b + d
  add-eq₁ refl refl = refl

  add-eq₂ : {n : ℕ} → (n + succ zero) ≡ succ n
  add-eq₂ {zero} = refl
  add-eq₂ {succ n} = cong succ add-eq₂

  ------------------------
  ----- inequalities -----
  ------------------------

  data _<_ : ℕ → ℕ → Set where
    base : {n : ℕ} → n < succ n
    step : {n m : ℕ} → n < m → n < succ m

  data _≥_ : ℕ → ℕ → Set where
    base : {n : ℕ} → n ≥ n
    step : {n m : ℕ} → n ≥ m → succ n ≥ m

  step₂-< : {n m : ℕ} → n < m → succ n < succ m
  step₂-< base = base
  step₂-< (step p) = step (step₂-< p)

  step₂-≥ : {n m : ℕ} → n ≥ m → succ n ≥ succ m
  step₂-≥ base = base
  step₂-≥ (step x) = step (step₂-≥ x)

  lemma-<-to-≥ : {n m : ℕ} → n < (succ m) → m ≥ n
  lemma-<-to-≥ {n} {m} p = {!   !}
  

  lemma-≥-zero : {n : ℕ} → n ≥ zero
  lemma-≥-zero {zero} = base
  lemma-≥-zero {succ x} = step lemma-≥-zero

  lemma-zero-<-succ : {n : ℕ} → zero < succ n
  lemma-zero-<-succ {zero} = base
  lemma-zero-<-succ {succ n} = step lemma-zero-<-succ

  step₂-≥-rev : {n m : ℕ} → succ n ≥ succ m → n ≥ m
  step₂-≥-rev base = base
  step₂-≥-rev (step base) = step base
  step₂-≥-rev (step (step x)) = step (step₂-≥-rev (step x))


  lemma-≥-to-≡ : {n m : ℕ} → n ≥ m → m ≥ n → n ≡ m
  lemma-≥-to-≡ {zero} {zero} p q = refl
  lemma-≥-to-≡ {(succ n)} {(succ m)} p q = cong succ (lemma-≥-to-≡ {n} {m} (step₂-≥-rev p) (step₂-≥-rev q))


  lemma-≥-<-to-≡ : {n m : ℕ} → n ≥ m → n < succ m → n ≡ m
  lemma-≥-<-to-≡ p q = lemma-≥-to-≡ p (lemma-<-to-≥ q)
  

  lemma-split-aux : {n s : ℕ} → n < s ⊎ n ≥ s → (succ n) < (succ s) ⊎ (succ n) ≥ (succ s)
  lemma-split-aux (left p) = left (step₂-< p)
  lemma-split-aux (right p) = right (step₂-≥ p)

  lemma-split-inequalities : (n s : ℕ) → n < s ⊎ n ≥ s
  lemma-split-inequalities zero zero = right base
  lemma-split-inequalities zero (succ s) = left lemma-zero-<-succ
  lemma-split-inequalities (succ n) zero = right lemma-≥-zero
  lemma-split-inequalities (succ n) (succ s) = lemma-split-aux (lemma-split-inequalities n s)