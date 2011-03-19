module StackedMonoids.Example where

open import Relation.Binary.PropositionalEquality renaming (refl to ≡-refl)

open import Data.Fin using (#_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec hiding ([_])
open import Data.ParallelVector

open import StackedMonoids.StackedMonoid

open import Level renaming (zero to z)

open import Algebra
open import Algebra.Structures

module N = CommutativeSemiring commutativeSemiring 

add-mul-stacked-monoid : StackedMonoid z z 2
add-mul-stacked-monoid = stackMonoid (setoid ℕ) 
                         (0 ∷ 1 ∷ []) 
                         (_+_ ∷ _*_ ∷ []) 
                         (N.+-assoc    ∷ N.*-assoc    ∷ []) 
                         (N.+-identity ∷ N.*-identity ∷ []) 
                         ((λ eq eq′ → cong₂ _+_ eq eq′) ∷ (λ eq eq′ → cong₂ _*_ eq eq′) ∷ [])

import StackedMonoids.Solver as S
open S add-mul-stacked-monoid

ex₁ : 0 + 0 ≡ 0
ex₁ = solve₁ 0 (ε (# 0) [ # 0 ] ε (# 0) := ε (# 0)) ≡-refl

ex₂ : (x : ℕ) → x * (x * x) ≡ (x * x) * x
ex₂ x = solve 1 (λ x → (x [ # 1 ] (x [ # 1 ] x)) 
                    := ((x [ # 1 ] x) [ # 1 ] x)) ≡-refl x