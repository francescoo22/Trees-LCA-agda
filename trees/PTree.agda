open import utilities.natural
-- open import utilities.vector
open import utilities.equality
open import utilities.range

module trees.PTree where

  -- some tries to implement a tree as a parent vector, I don't know if it the way to go
  -- I have to understand if it is better to use a parent function from distinct-tree or this

  data Vecᵣ (A : Set) : ℕ → Set where
    []  : Vecᵣ A zero
    _∷_ : {n : ℕ} → Vecᵣ A n → A → Vecᵣ A (succ n)


  data PTree : {n : ℕ} → Vecᵣ ℕ n → Set where
    base : PTree ([] ∷ zero)
    step : {n : ℕ} → {t : Vecᵣ ℕ n} → (x : ℕ) → PTree t → x < n → PTree (t ∷ x)


  {-
           0
          / \
         1   2
            / \
           3   6
          /  \
         4    5

      this LBTree is represented by the following PTree vecotr:
      pos : 0 1 2 3 4 5 6
      val : 0 0 0 2 3 3 2
  -}

  -- considerare l'idea di fare ℕ ⊎ nil per il tipo di ritorno
  parent : {n : ℕ} → {t : Vecᵣ ℕ n} → (x : ℕ) → PTree t → x ∈ zero ⋯ n → ℕ
  parent x base q = zero
  parent {(succ n-1)} x (step par ptree x₁) q with split-equality (succ n-1) x
  ... | left n≡x = par
  ... | right ¬n≡x = {! parent x-1 ptree bohhh  !}
  -- parent {n} x p q with split-equality n x
  -- ... | left n≡x = {!   !}
  -- ... | right ¬n≡x = {!   !}

  -- vector in which at each position i, v[i] = label of the parent of the node labelled with import
  -- except from the root which has parent equal to the value passed in input

  -- parent-tree-vec : (t : LBTree) → ℕ → Vec ℕ (LBTree-size t)
  -- parent-tree-vec (l-leaf x) n = n ∷ []
  -- parent-tree-vec (l-node x l r) n = n ∷ ((parent-tree-vec l x) +++ (parent-tree-vec r x)) 