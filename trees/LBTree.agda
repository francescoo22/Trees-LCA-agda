
{-# OPTIONS --allow-unsolved-metas #-}

open import utilities.natural
open import trees.BTree
open import utilities.list
open import utilities.equality
open import utilities.vector
open import utilities.range
open import utilities.optional


module trees.LBTree where 
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
  lemma-LBT-size (node l r) = cong succ (add-eq₁ (lemma-LBT-size l) (lemma-LBT-size r))

  lemma-BT-LBT-size : {n : ℕ} → (t : BTree) → BTree-size t ≡ LBTree-size (label t n)
  lemma-BT-LBT-size leaf = refl
  lemma-BT-LBT-size (node l r) = cong succ (add-eq₁ (lemma-BT-LBT-size l) (lemma-BT-LBT-size r))


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


  lemma-unique-labelling : (t : BTree) → (n s : ℕ) → n ∈ s ⋯ (s + BTree-size t) → n ∈ label t s
  lemma-unique-labelling leaf n s p = lemma-≡-∈ (symm (lemma-singleton-range (lemma-eq-range p add-eq₂))) ∈-leaf
  lemma-unique-labelling (node l r) n s p with lemma-split-range (succ s) p
  ... | left x = lemma-≡-∈ (symm (lemma-singleton-range x)) ∈-node
  ... | right x with lemma-split-range (succ s + BTree-size l) x
  ... | left x₁ = ∈-left (lemma-unique-labelling l n (succ s) x₁)
  ... | right x₁ = ∈-right (lemma-unique-labelling r n (succ (s + BTree-size l)) (lemma-eq-range x₁ add-eq₃))
    

  lemma-unique-labelling₀ : (t : BTree) → (n : ℕ) → n ∈ zero ⋯ BTree-size t → n ∈ label t zero
  lemma-unique-labelling₀ t n p = lemma-unique-labelling t n zero p


  --------------------------------
  -------- label by depth --------
  --------------------------------

  depth-label-aux : BTree → ℕ → LBTree 
  depth-label-aux leaf n = l-leaf n
  depth-label-aux (node l r) n = l-node n (depth-label-aux l (succ n)) (depth-label-aux r (succ n))

  depth-label : BTree → LBTree -- label eache node/leaf with a value correspondign to his depth
  depth-label t = depth-label-aux t zero

  -- depth : (t : LBTree) → (n : ℕ) → n ∈ t → ℕ -- va fatto passando un abitante di unique-labelled-tree (da implementare)
  -- depth .(l-leaf n) n ∈-leaf = zero -- anche se tolgo il punto non cambia nulla
  -- depth .(l-node n _ _) n ∈-node = zero
  -- depth (l-node _ l _) n (∈-left p) = succ (depth l n p )
  -- depth (l-node _ _ r) n (∈-right p) = succ (depth r n p)

  


  -- parent-tree-list : (t : LBTree) → ℕ → List ℕ
  -- parent-tree-list (l-leaf x) n = {!   !}
  -- parent-tree-list (l-node x t t₁) n = {!   !}


