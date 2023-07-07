open import trees.LBTree
open import trees.distinct-tree
open import utilities.natural
open import utilities.equality

module trees.LCA where
  -- just a draft of Least Common Ancestor algorithm, 
  -- probably to much work to achieve an implementation + proof of correctness

  -- data LCA : {t : LBTree} → distinct-tree t → (x y : ℕ) → x ∈ t → y ∈ t → Set where

  LCA-alg : {t : LBTree} → distinct-tree t → (x y : ℕ) → x ∈ t → y ∈ t → ℕ
  LCA-alg dist x y x∈t y∈t with split-equality x y
  ... | left x≡y = x
  ... | right ¬x≡y with split-equality (depth dist x x∈t) (depth dist y y∈t)
  ... | left same-depth = LCA-alg dist (parent dist x x∈t) (parent dist y y∈t) {!   !} {!   !}
  ... | right diff-depth = {!   !} -- splittare per depth1 > o < di depth2
  
  
  -- split-equality (depth dist x x∈t) (depth dist y y∈t)
  -- ... | left x₁ with split-equality x y
  -- ... | right x₁ = {!   !}