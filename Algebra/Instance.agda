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

Semigroup : Structure
Semigroup = record
  { arities = 2 ∷ []
  ; laws    = build (λ _∙_ → (2 , λ x y z → ((x ∙ y) ∙ z) == (x ∙ (y ∙ z))) ∷ [])
  }

Lava : Structure
Lava = record
  { arities = 2 ∷ []
  ; laws    = build (λ _∙_ → (1 , λ x y → (x ∙ y) == (y ∙ x)) ∷ [])
  }

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

Distributive : Structure
Distributive = record
  { arities = 2 ∷ 2 ∷ []
  ; laws    = build (λ _+_ _*_ → (2 , λ x y z → (x * (y + z)) == ((x * y) + (x * z)))
                               ∷ (2 , λ x y z → ((x + y) * z) == ((x * z) + (y * z)))
                               ∷ [])
  }

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

Ring : Structure
Ring = record
  { arities = 2 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ []
  ; laws    = from⟨ AbelianGroup ⟩ (λ #0 #1 -_ _+_ _*_ → _+_ ∷ -_ ∷ #0 ∷ [])
           ++ from⟨ Monoid       ⟩ (λ #0 #1 -_ _+_ _*_ → _*_ ∷ #1 ∷ [])
           ++ from⟨ Distributive ⟩ (λ #0 #1 -_ _+_ _*_ → _*_ ∷ _+_ ∷ [])
  }
