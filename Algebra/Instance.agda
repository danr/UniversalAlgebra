module Algebra.Instance where

open import Algebra.Menu
open import Algebra.FromStructure

open import Data.List using (_∷_ ; [] ; _++_)
open import Data.Fin hiding (_+_)
open import Data.ParallelVector using (par-lookup)
open import Data.ParallelList using (_∷_ ; [] ; fromParList)
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Level

Semigroup : Structure
Semigroup = record
  { arities = 2 ∷ []
  ; laws    = build (λ _∙_ → (2 , λ x y z → (x ∙ (y ∙ z)) == ((x ∙ y) ∙ z)) ∷ [])
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

Ring : Structure
Ring = record
  { arities = 2 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ []
  ; laws    = from⟨ AbelianGroup ⟩ (λ #0 #1 -_ _+_ _*_ → _+_ ∷ -_ ∷ #0 ∷ [])
           ++ from⟨ Monoid       ⟩ (λ #0 #1 -_ _+_ _*_ → _*_ ∷ #1 ∷ [])
           ++ build (λ #0 #1 -_ _+_ _*_ → (2 , λ x y z → (x * (y + z)) == ((x * y) + (x * z)))
                                        ∷ (2 , λ x y z → ((x + y) * z) == ((x * z) + (y * z)))
                                        ∷ [])
  }


{-
data ℤ₂ : Set where
  #0 #1 : ℤ₂

_+′_ : ℤ₂ → ℤ₂ → ℤ₂
#0 +′ #0 = #0
#1 +′ #0 = #1
#0 +′ #1 = #1
#1 +′ #1 = #0

+-comm : ∀ x y → x +′ y ≡ y +′ x
+-comm #0 #0 = refl
+-comm #0 #1 = refl
+-comm #1 #0 = refl
+-comm #1 #1 = refl

open import Data.Sum

ℤ₂-Lava : Instance zero zero Lava
ℤ₂-Lava = record 
  { setoid = setoid ℤ₂
  ; ⟦op⟧   = _+′_ ∷ []
  ; ⟦law⟧  = (λ x y → +-comm x y) ∷ []
  ; ⟦cong⟧ = (λ eq₁ eq₂ → cong₂ _+′_ eq₁ eq₂) ∷ []
  }

Commutativity : ∀ x y → x +′ y ≡ y +′ x
Commutativity = par-lookup (fromParList (Instance.⟦law⟧ ℤ₂-Lava)) zero
-}

