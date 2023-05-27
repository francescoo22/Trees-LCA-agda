open import natural
open import BTree
open import list
open import equality

module LBTree where 
  data LBTree : Set where -- Labelled binary tree
    l-leaf : ℕ → LBTree
    l-node : ℕ → LBTree → LBTree → LBTree

  LBTree-size : LBTree → ℕ
  LBTree-size (l-leaf _) = succ zero
  LBTree-size (l-node _ l r) = succ (LBTree-size l + LBTree-size r)

  LBTree-height : LBTree → ℕ
  LBTree-height (l-leaf _) = succ zero
  LBTree-height (l-node _ l r) = succ (max (LBTree-height l) (LBTree-height r))

  label : BTree → ℕ → LBTree -- label each node/leaf with a unique ℕ starting from the given one
  label leaf n = l-leaf n
  label (node l r) n = l-node n (label l (succ n)) (label r (succ (n + BTree-size l)))

  lemma-LBT-size : {x y : ℕ} → (t : BTree) → LBTree-size (label t x) ≡ LBTree-size (label t y)
  lemma-LBT-size leaf = refl
  lemma-LBT-size (node l r) = cong succ (add-aux₁ (lemma-LBT-size l) (lemma-LBT-size r))

  lemma-BT-LBT-size : {n : ℕ} → (t : BTree) → BTree-size t ≡ LBTree-size (label t n)
  lemma-BT-LBT-size leaf = refl
  lemma-BT-LBT-size (node l r) = cong succ (add-aux₁ (lemma-BT-LBT-size l) (lemma-BT-LBT-size r))

  labels-list : LBTree → List ℕ
  labels-list (l-leaf x) = x ∷ []
  labels-list (l-node x l r) = x ∷ (labels-list l ++ labels-list r)

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



  -- first naturals (0 ∷ 1 ∷ 2 ∷ []) 3
  prova : first-naturals (zero ∷ (succ zero ∷ (succ (succ zero) ∷ []))) (succ (succ (succ zero)))
  prova = step (step base)

  -- boh-lemma : (x y : ℕ) → (t : BTree) → list-size (labels-list (label t x)) ≡ list-size (labels-list (label t y))
  -- boh-lemma x y leaf = refl
  -- boh-lemma x y (node l r) with label l (succ x)
  -- ... | p with label l (succ y)
  -- ... | q = {!   !}

  -- tree-size-≡-labels-size : {n : ℕ} → (t : BTree) → BTree-size t ≡ list-size (labels-list (label t n))
  -- tree-size-≡-labels-size leaf = refl
  -- tree-size-≡-labels-size (node l r) = {!   !}

  -- -- the list obtained by calling "labels-list" on a tree t labelled using the function "label" is 
  -- -- 0 :: 1 :: 2 :: ... :: size(t) - 1
  -- lemma : (t : BTree) → first-naturals (labels-list (label t zero)) (BTree-size t)
  -- lemma leaf = base
  -- lemma (node l r) with labels-list (label l (succ zero))
  -- ... | l_list with (labels-list (label r (succ (BTree-size l))))
  -- ... | r_list with BTree-size l
  -- ... | sl with BTree-size r
  -- lemma (node l r) | [] | [] | sl | sr = {!  base !}
  -- lemma (node l r) | [] | y ∷ ys | sl | sr = {!   !}
  -- lemma (node l r) | x ∷ xs | r_list | sl | sr = {!   !}


