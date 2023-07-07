open import utilities.equality
open import utilities.natural
open import utilities.list

module trees.BTree where

  data BTree : Set where
    leaf : BTree
    node : BTree → BTree → BTree

  sample_tree : BTree
  sample_tree = node leaf (node (node leaf leaf) leaf)

  {-    node
        /  \
    leaf  node
          /  \
        node leaf
        /  \
      leaf leaf
  -}

  BTree-size : BTree → ℕ
  BTree-size leaf = succ zero
  BTree-size (node l r) = succ (BTree-size l + BTree-size r)

  BTree-height : BTree → ℕ
  BTree-height leaf = succ zero
  BTree-height (node l r) = succ (max (BTree-height l) (BTree-height r))

 