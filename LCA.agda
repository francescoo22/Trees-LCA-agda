open import LBTree
open import natural
open import equality

module LCA where
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