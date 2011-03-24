module BooleanAlgebra.Member where

open import Data.Maybe
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- T :   x is in the set
-- N : ¬ x is in the set
-- F :   x is not in the set

data Member : Set where
  T N F : Member

_⋀_ : Member → Member → Maybe Member
T ⋀ N = nothing      --   x ∧ ¬ x ≈ ⊥
N ⋀ T = nothing      -- ¬ x ∧   x ≈ ⊥
T ⋀ m = just T       --   x ∧   x ≈   x ,   x ≈   x 
N ⋀ m = just N       -- ¬ x ∧ ¬ x ≈ ¬ x , ¬ x ≈ ¬ x
F ⋀ m = just m

not : Member → Member
not T = N
not N = T
not F = F

data _<_ : Member → Member → Set where
  T<N : T < N
  T<F : T < F
  N<F : N < F

Member-Order : StrictTotalOrder _ _ _
Member-Order = record
    { Carrier = Member
    ; _≈_     = _≡_
    ; _<_     = _<_
    ; isStrictTotalOrder = record
      { isEquivalence = isEquivalence
      ; trans = transitive
      ; compare = compare
      ; <-resp-≈ = (λ {x} → subst (_<_ x))
                  , λ {y} → subst (λ x → x < y)
      }
    }
  where
    transitive : ∀ {i j k} → i < j → j < k → i < k
    transitive T<N N<F = T<F
    transitive T<F ()
    transitive N<F ()

    compare : (x y : Member) → Tri (x < y) (x ≡ y) (y < x)
    compare T T = tri≈ (λ ()) refl (λ ())
    compare T N = tri< T<N (λ ()) (λ ())
    compare T F = tri< T<F (λ ()) (λ ())
    compare N T = tri> (λ ()) (λ ()) T<N
    compare N N = tri≈ (λ ()) refl (λ ())
    compare N F = tri< N<F (λ ()) (λ ())
    compare F T = tri> (λ ()) (λ ()) T<F
    compare F N = tri> (λ ()) (λ ()) N<F
    compare F F = tri≈ (λ ()) refl (λ ())
