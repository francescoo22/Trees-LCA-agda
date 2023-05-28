open import natural

module vector where
  infixr 5 _∷_
  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

  infixr 5 _+++_

  _+++_ : {A : Set} {n m : ℕ} → Vec A m → Vec A n → Vec A (m + n)
  []       +++ ys = ys
  (x ∷ xs) +++ ys = x ∷ (xs +++ ys)