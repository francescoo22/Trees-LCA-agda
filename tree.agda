-- infix 5 _≡_

-- data _≡_ {X : Set} : X → X → Set where
--   refl : {a : X} → a ≡ a


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

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

append : {A : Set} → List A → A → List A
append [] y = y ∷ []
append (x ∷ xs) y = x ∷ (append xs y)

data first-naturals : List ℕ → ℕ → Set where
  base : first-naturals (zero ∷ []) (succ zero)
  step : {l : List ℕ} {n : ℕ} → first-naturals l n → first-naturals (append l n) (succ n)

_++_ : {A : Set} → List A → List A → List A
[] ++ y = y
(x ∷ xs) ++ y = x ∷ (xs ++ y)
  
data BTree : Set where
  leaf : BTree
  node : BTree → BTree → BTree

sample_tree : BTree
sample_tree = node leaf (node (node leaf leaf) leaf)

{-   node
      /  \
  leaf  node
        /  \
      node leaf
      /  \
    leaf leaf
-}

size : BTree → ℕ
size leaf = succ zero
size (node l r) = (succ zero) + (size l + size r)

height : BTree → ℕ
height leaf = succ zero
height (node l r) = succ (max (height l) (height r))

data LBTree : Set where -- Labelled binary tree
  l-leaf : ℕ → LBTree
  l-node : ℕ → LBTree → LBTree → LBTree

label : BTree → ℕ → LBTree -- label each node/leaf with a unique ℕ starting from the given one
label leaf n = l-leaf n
label (node l r) n = l-node n (label l (succ n)) (label r (succ (n + size l)))

labels-list : LBTree → List ℕ
labels-list (l-leaf x) = x ∷ []
labels-list (l-node x l r) = x ∷ (labels-list l ++ labels-list r)

-- the list obtained by calling "labels-list" on a tree t labelled using the function "label" is 
-- 0 :: 1 :: 2 :: ... :: size(t) - 1
lemma : (t : BTree) → first-naturals (labels-list (label t zero)) (size t)
lemma t = {!   !}

