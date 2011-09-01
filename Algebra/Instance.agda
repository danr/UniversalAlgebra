module Algebra.Instance where

open import Algebra.Menu
open import Algebra.FromStructure

open import Data.List using (_∷_ ; [] ; _++_)
open import Data.Fin hiding (_+_)
open import Data.ParallelList using (_∷_ ; [])
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Level

-- A Semigroup is an algebraic structure with one binary operator (a Magma),
-- with the additional constraint that the operator is associative.
-- This is expressed as follows in this DSL.
Semigroup : Structure
Semigroup = record
  { arities = 2 ∷ []
  -- The build keyword gives you the operators of the structure as an argument
  -- to a lambda function. The 2 in the tuple refers to this being a law with
  -- suc 2 = 3 arguments, and then a new lambda function with those arguments
  -- expressing the law of associativity.
  ; laws    = build (λ _∙_ → (2 , λ x y z → ((x ∙ y) ∙ z) == (x ∙ (y ∙ z))) ∷ [])
  }

-- Lava is my name for a Commutative Magma, also known as Steiner Magma.
Lava : Structure
Lava = record
  { arities = 2 ∷ []
  ; laws    = build (λ _∙_ → (1 , λ x y → (x ∙ y) == (y ∙ x)) ∷ [])
  }

-- When we enlarge this for Monoids, we can use the associativity expressed 
-- in the Semigroup, by letting the binary operator inherit the laws 
-- (of associativity) from the Semigroup.
Monoid : Structure
Monoid = record
  { arities = 2 ∷ 0 ∷ []
  ; laws    = from⟨ Semigroup ⟩ (λ ε _∙_ → _∙_ ∷ [])
           ++ build (λ ε _∙_ → (0 , λ x → (x ∙ ε) == x) 
                             ∷ (0 , λ x → (ε ∙ x) == x) 
                             ∷ []) 
  } 

CommutativeMonoid : Structure
CommutativeMonoid = record
  { arities = 2 ∷ 0 ∷ []
  ; laws    = from⟨ Monoid ⟩ (λ ε _∙_ → _∙_ ∷ ε ∷ [])
           ++ from⟨ Lava   ⟩ (λ ε _∙_ → _∙_ ∷ [])
  }

Group : Structure
Group = record
  { arities = 2 ∷ 1 ∷ 0 ∷ []
  ; laws    = from⟨ Monoid ⟩ (λ ε _⁻¹ _∙_ → _∙_ ∷ ε ∷ [])
           ++ build (λ ε _⁻¹ _∙_ → (0 , λ x → (x ∙ (x ⁻¹)) == ε)
                                 ∷ (0 , λ x → ((x ⁻¹) ∙ x) == ε) 
                                 ∷ [])
  }

AbelianGroup : Structure
AbelianGroup = record
  { arities = 2 ∷ 1 ∷ 0 ∷ []
  ; laws    = from⟨ Group ⟩ (λ ε _⁻¹ _∙_ → _∙_ ∷ _⁻¹ ∷ ε ∷ [])
           ++ from⟨ Lava  ⟩ (λ ε _⁻¹ _∙_ → _∙_ ∷ [])
  }

-- Not a real structure per se, but describes that the two operators distribute.
Distributive : Structure
Distributive = record
  { arities = 2 ∷ 2 ∷ []
  ; laws    = build (λ _+_ _*_ → (2 , λ x y z → (x * (y + z)) == ((x * y) + (x * z)))
                               ∷ (2 , λ x y z → ((x + y) * z) == ((x * z) + (y * z)))
                               ∷ [])
  }

-- Now we can simply express structures as this Commutative Semiring
CommutativeSemiring : Structure
CommutativeSemiring = record
  { arities = 2 ∷ 2 ∷ 0 ∷ 0 ∷ []
  ; laws    = from⟨ CommutativeMonoid ⟩ (λ #0 #1 _+_ _*_ → _+_ ∷ #0 ∷ [])
           ++ from⟨ CommutativeMonoid ⟩ (λ #0 #1 _+_ _*_ → _*_ ∷ #1 ∷ [])
           ++ from⟨ Distributive      ⟩ (λ #0 #1 _+_ _*_ → _*_ ∷ _+_ ∷ [])
           ++ build (λ #0 #1 _+_ _*_ → (0 , λ x → (x * #0) == #0)
                                     ∷ (0 , λ x → (#0 * x) == #0)
                                     ∷ [])
  }

-- Or even a normal Ring.
Ring : Structure
Ring = record
  { arities = 2 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ []
  ; laws    = from⟨ AbelianGroup ⟩ (λ #0 #1 -_ _+_ _*_ → _+_ ∷ -_ ∷ #0 ∷ [])
           ++ from⟨ Monoid       ⟩ (λ #0 #1 -_ _+_ _*_ → _*_ ∷ #1 ∷ [])
           ++ from⟨ Distributive ⟩ (λ #0 #1 -_ _+_ _*_ → _*_ ∷ _+_ ∷ [])
  }
