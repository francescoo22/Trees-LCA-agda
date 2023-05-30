open import natural
open import BTree
open import list
open import equality
open import vector
open import range

module LBTree where 
  data LBTree : Set where -- Labelled binary tree
    l-leaf : ℕ → LBTree
    l-node : ℕ → LBTree → LBTree → LBTree

  data _∼_ : BTree → LBTree → Set where -- shape equivalence
    ∼leaf : {n : ℕ} → leaf ∼ (l-leaf n)
    ∼node : {n : ℕ} {l₁ r₁ : BTree} {l₂ r₂ : LBTree} → l₁ ∼ l₂ → r₁ ∼ r₂ → node l₁ r₁ ∼ l-node n l₂ r₂

  data _∈_ : ℕ → LBTree → Set where
    ∈-leaf  : {n : ℕ} → n ∈ l-leaf n
    ∈-node  : {n : ℕ} {l r : LBTree} → n ∈ l-node n l r
    ∈-left  : {n x : ℕ} {l r : LBTree} → n ∈ l → n ∈ l-node x l r
    ∈-right : {n x : ℕ} {l r : LBTree} → n ∈ r → n ∈ l-node x l r

  lemma-≡-∈ : {t : LBTree} {n m : ℕ} → n ≡ m → n ∈ t → m ∈ t
  lemma-≡-∈ refl n∈t = n∈t

  LBTree-size : LBTree → ℕ
  LBTree-size (l-leaf _) = succ zero
  LBTree-size (l-node _ l r) = succ (LBTree-size l + LBTree-size r)

  LBTree-height : LBTree → ℕ
  LBTree-height (l-leaf _) = succ zero
  LBTree-height (l-node _ l r) = succ (max (LBTree-height l) (LBTree-height r))

  labels-list : LBTree → List ℕ
  labels-list (l-leaf x) = x ∷ []
  labels-list (l-node x l r) = x ∷ (labels-list l ++ labels-list r)

  ---------------------------------
  ----- unique tree labelling -----
  ---------------------------------

  label : BTree → ℕ → LBTree -- label each node/leaf with a unique ℕ starting from the given one
  label leaf n = l-leaf n
  label (node l r) n = l-node n (label l (succ n)) (label r (succ (n + BTree-size l)))

  lemma-BT-∼-label : {n : ℕ} → (t : BTree) → t ∼ label t n
  lemma-BT-∼-label leaf = ∼leaf
  lemma-BT-∼-label (node l r) = ∼node (lemma-BT-∼-label l) (lemma-BT-∼-label r)

  lemma-LBT-size : {x y : ℕ} → (t : BTree) → LBTree-size (label t x) ≡ LBTree-size (label t y)
  lemma-LBT-size leaf = refl
  lemma-LBT-size (node l r) = cong succ (add-aux₁ (lemma-LBT-size l) (lemma-LBT-size r))

  lemma-BT-LBT-size : {n : ℕ} → (t : BTree) → BTree-size t ≡ LBTree-size (label t n)
  lemma-BT-LBT-size leaf = refl
  lemma-BT-LBT-size (node l r) = cong succ (add-aux₁ (lemma-BT-LBT-size l) (lemma-BT-LBT-size r))


  lemma-BT-list-size : {n : ℕ} → (t : BTree) → BTree-size t ≡ list-size (labels-list (label t n))
  lemma-BT-list-size leaf = refl
  lemma-BT-list-size {n} (node l r) = begin
    succ (BTree-size l + BTree-size r) 
      ≡⟨ cong (λ x → succ (x + BTree-size r)) (lemma-BT-list-size l) ⟩
    succ (list-size (labels-list (label l (succ n))) + BTree-size r) 
      ≡⟨ cong (λ x → succ (list-size (labels-list (label l (succ n))) + x)) (lemma-BT-list-size r) ⟩
    succ (list-size (labels-list (label l (succ n))) + list-size (labels-list (label r (succ (n + BTree-size l)))))
      ≡⟨ cong succ (symm (lemma-++-size
        (labels-list (label l (succ n)))
        (labels-list (label r (succ (n + BTree-size l))))
      )) ⟩
    succ (list-size (labels-list (label l (succ n)) ++ labels-list (label r (succ (n + BTree-size l))))) ∎

  TODO : (t : BTree) → (n s : ℕ) → n ≥ s → n < (s + BTree-size t) → n ∈ label t s
  TODO leaf n s p q = lemma-≡-∈ {!   !} ∈-leaf -- basta qualche proprietà sulle diseguaglianze
  TODO (node l r) n .n base q = ∈-node
  TODO (node l r) .(succ _) s (step p) q = {!   !} -- devo splittare la diseguaglianza nel caso in cui sono in l o r

  boh : (t : BTree) → (n s : ℕ) → n ∈ s ⋯ (s + BTree-size t) → n ∈ label t s
  boh leaf n s p = {!   !}
  boh (node t t₁) n s p = {!   !}

  lemma-unique-labelling : (t : BTree) → (n : ℕ) → n < BTree-size t → n ∈ label t zero
  lemma-unique-labelling t n p =  TODO t n zero lemma-≥-zero p


  --------------------------------
  -------- label by depth --------
  --------------------------------

  depth-label-aux : BTree → ℕ → LBTree 
  depth-label-aux leaf n = l-leaf n
  depth-label-aux (node l r) n = l-node n (depth-label-aux l (succ n)) (depth-label-aux r (succ n))

  depth-label : BTree → LBTree -- label eache node/leaf with a value correspondign to his depth
  depth-label t = depth-label-aux t zero


  -- -- first naturals (0 ∷ 1 ∷ 2 ∷ []) 3
  -- prova : first-naturals (zero ∷ (succ zero ∷ (succ (succ zero) ∷ []))) (succ (succ (succ zero)))
  -- prova = step (step base)

  -- -- the list obtained by calling "labels-list" on a tree t labelled using the function "label" is 
  -- -- 0 :: 1 :: 2 :: ... :: size(t) - 1
  -- -- pre dimostrarlo l'idea dovrebbe essere: 
  -- -- dichiaro il tipo "lista from x to y" e mostro che questo é lista from 0 to size(t) - 1
  -- lemma : (t : BTree) → first-naturals (labels-list (label t zero)) (BTree-size t)
  -- lemma leaf = base
  -- lemma (node l r) = {!   !}

  -- parent-tree-list : (t : LBTree) → ℕ → List ℕ
  -- parent-tree-list (l-leaf x) n = {!   !}
  -- parent-tree-list (l-node x t t₁) n = {!   !}

  -- vector in which at each position i, v[i] = label of the parent of the node labelled with import
  -- except from the root which has parent equal to the value passed in input
  parent-tree-vec : (t : LBTree) → ℕ → Vec ℕ (LBTree-size t)
  parent-tree-vec (l-leaf x) n = n ∷ []
  parent-tree-vec (l-node x l r) n = n ∷ ((parent-tree-vec l x) +++ (parent-tree-vec r x)) 