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

-- We just stack _+_ and _*_ monoids on top of each other.
-- Note that we cannot use any distributivity in the laws
add-mul-stacked-monoid : StackedMonoid z z 2
add-mul-stacked-monoid = stackMonoid (setoid ℕ) 
                         (0 ∷ 1 ∷ []) 
                         (_+_ ∷ _*_ ∷ []) 
                         (N.+-assoc    ∷ N.*-assoc    ∷ []) 
                         (N.+-identity ∷ N.*-identity ∷ []) 
                         ((λ eq eq′ → cong₂ _+_ eq eq′) ∷ (λ eq eq′ → cong₂ _*_ eq eq′) ∷ [])

-- Open the solver
import StackedMonoids.Solver as S
open S add-mul-stacked-monoid

infix 10 _:+_ _:*_

-- These should come for free (somehow)
_:+_ : ∀ {v} → Expr {v} → Expr {v} → Expr {v}
x :+ y = x [ # 0 ] y

_:*_ : ∀ {v} → Expr {v} → Expr {v} → Expr {v}
x :* y = x [ # 1 ] y

:0 : ∀ {v} → Expr {v}
:0 = ε (# 0)

:1 : ∀ {v} → Expr {v}
:1 = ε (# 1)

-- Some examples
ex₁ : 0 + 0 ≡ 0
ex₁ = solve 0 (:0 :+ :0 := :0) ≡-refl

ex₂ : (x : ℕ) → x * (x * x) ≡ (x * x) * x
ex₂ = solve 1 (λ x → x :* (x :* x) := (x :* x) :* x) ≡-refl

ex₃ : (a b c d e : ℕ) → (a + ((b * c) * d)) + e 
                      ≡ a + (b * (c * (d * 1)) + (e + 0))
ex₃ = solve 5 (λ a b c d e → ((a :+ ((b :* c) :* d)) :+ e)
                          := (a :+ ((b :* (c :* (d :* :1))) :+ (e :+ :0)))) ≡-refl
                           
