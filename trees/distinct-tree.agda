{-# OPTIONS --allow-unsolved-metas #-}

open import trees.BTree
open import trees.LBTree
open import utilities.optional
open import utilities.equality
open import utilities.natural

module trees.distinct-tree where
  data distinct-tree : LBTree → Set where
    base : {x : ℕ} → distinct-tree (l-leaf x)
    step : {x : ℕ} {l r : LBTree} → 
                    ¬ (x ∈ l) → ¬ (x ∈ r) →
                    distinct-tree l →
                    distinct-tree r →
                    ({y : ℕ} → (y ∈ l) → (y ∈ r) → ⊥) →
                    distinct-tree (l-node x l r)


  distinct-labelling : (x : ℕ) → (t : BTree) → distinct-tree (label t x)
  distinct-labelling x leaf = base
  distinct-labelling x (node l r) = step 
    (lemma-¬-∈ l x (succ x) base)
    (lemma-¬-∈ r x (succ (x + BTree-size l)) step₄-<) 
    (distinct-labelling (succ x) l) 
    (distinct-labelling (succ (x + BTree-size l)) r) 
    {!   !}

  depth : {t : LBTree} → distinct-tree t → (n : ℕ) → n ∈ t → ℕ
  depth {l-leaf x} dist n p = zero
  depth {l-node x l r} dist .x ∈-node = zero
  depth {l-node x l r} (step x₁ x₂ dist dist₁ x₃) n (∈-left p) = succ (depth dist n p)
  depth {l-node x l r} (step x₁ x₂ dist dist₁ x₃) n (∈-right p) = succ (depth dist₁ n p)

  
  parent : {t : LBTree} → distinct-tree t → (n : ℕ) → n ∈ t → Optional ℕ
  parent {l-leaf x} dist n n∈t = none
  parent {l-node x l r} dist .x ∈-node = none
  
  parent {l-node x .(l-leaf n) r} dist n (∈-left ∈-leaf) = some x
  parent {l-node x .(l-node n _ _) r} dist n (∈-left ∈-node) = some x
  parent {l-node x l r} (step x₁ x₂ dist dist₁ x₃) n (∈-left (∈-left n∈l₁)) = parent dist n (∈-left n∈l₁)
  parent {l-node x .(l-node _ _ _) r} dist n (∈-left (∈-right n∈l)) = {!   !}

  parent {l-node x l r} dist n (∈-right n∈r) = {!   !}
  -- parent {l-leaf x} dist n p = none -- n is in the root → NO parent
  -- parent {l-node x l r} dist .x ∈-node = none -- n is in the root → NO parent
  -- parent {l-node x .(l-leaf n) r} dist n (∈-left ∈-leaf) = some x -- n is the son of the node x
  -- parent {l-node x .(l-node n _ _) r} dist n (∈-left ∈-node) = some x -- n is the son of the node x
  -- parent {l-node x .(l-node _ _ _) r} dist n ((∈-left n∈l)) = {!   !}
  -- -- parent {l-node x .(l-node _ _ _) r} dist n (∈-left (∈-right n∈l)) = parent {!   !} n n∈l -- n is somewhere in the left but not the next node
  -- parent {l-node x l .(l-leaf n)} dist n (∈-right ∈-leaf) = some x
  -- parent {l-node x l .(l-node n _ _)} dist n (∈-right ∈-node) = some x
  -- parent {l-node x l .(l-node _ _ _)} dist n (∈-right (∈-left p)) = {!   !}
  -- parent {l-node x l .(l-node _ _ _)} dist n (∈-right (∈-right p)) = {!   !} -- stesso pattern matching del caso sopra 