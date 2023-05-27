module natural where
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  succ a + b = succ (a + b)

  max : ℕ → ℕ → ℕ
  max zero b = b
  max (succ a) zero = succ a
  max (succ a) (succ b) = succ (max a b)