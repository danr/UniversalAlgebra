module StackedMonoids.NodeDecoratedListTree where

-- Tree where every branch has a list of more trees
-- The nodes (branches) are decorated with a node,
-- such that the union of two trees with of the same 
-- node type will just append the lists.

open import Data.Bool using (if_then_else_)
open import Data.List using (List ; _∷_ ; [] ; [_] ; _++_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

data NLT (A N : Set) : Set where
  leaf   : (x : A) → NLT A N
  branch : (n : N) (t : List (NLT A N)) → NLT A N
  
module Operations (A N : Set) (_≟_ : Decidable (_≡_ {A = N})) where

  _≟_then_else_ : ∀ {A : Set} → N → N → A → A → A
  n ≟ n′ then x else y = if ⌊ n ≟ n′ ⌋ then x else y

  -- Union of two decorated trees under a certain node type n₀
  _∪_⟨_⟩ : NLT A N → NLT A N → N → NLT A N
  leaf x     ∪ leaf x′      ⟨ n₀ ⟩ = branch n₀ (leaf x ∷ leaf x′ ∷ [])
  leaf x     ∪ branch n t   ⟨ n₀ ⟩ = n₀ ≟ n then branch n (leaf x ∷ t) 
                                            else branch n₀ (leaf x ∷ branch n t ∷ [])
  branch n t ∪ leaf x       ⟨ n₀ ⟩ = n₀ ≟ n then branch n (t ++ [ leaf x ])
                                            else branch n₀ (branch n t ∷ leaf x ∷ [])
  branch n t ∪ branch n′ t′ ⟨ n₀ ⟩ = 
      n₀ ≟ n then (n₀ ≟ n′ then branch n (t ++ t′) 
                           else branch n (t ++ [ branch n′ t′ ])) 
             else (n₀ ≟ n′ then branch n′ ([ branch n t ] ++ t′) 
                           else branch n₀ (branch n t ∷ branch n′ t′ ∷ []))
