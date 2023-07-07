open import utilities.natural
open import utilities.equality

module utilities.list where
  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  append : {A : Set} → List A → A → List A
  append [] y = y ∷ []
  append (x ∷ xs) y = x ∷ (append xs y)

  list-size : {A : Set} → List A → ℕ
  list-size [] = zero
  list-size (x ∷ xs) = succ (list-size xs)


  infixr 5 _++_
  
  _++_ : {A : Set} → List A → List A → List A
  [] ++ y = y
  (x ∷ xs) ++ y = x ∷ (xs ++ y)

  lemma-++-size : {A : Set} → (xs ys : List A) → list-size (xs ++ ys) ≡ list-size xs + list-size ys
  lemma-++-size [] ys = refl
  lemma-++-size (x ∷ xs) ys = cong succ (lemma-++-size xs ys)