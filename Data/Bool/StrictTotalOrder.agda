module Data.Bool.StrictTotalOrder where

open import Data.Bool
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

data _<_ : Bool → Bool → Set where
  F<T : false < true

BoolStrictTotalOrder : StrictTotalOrder _ _ _
BoolStrictTotalOrder = record 
  { Carrier = Bool
  ; _≈_ = _≡_
  ; _<_ = _<_
  ; isStrictTotalOrder = record 
    { isEquivalence = isEquivalence
    ; trans = transitive
    ; compare = compare
    ; <-resp-≈ = (λ {x} → subst (_<_ x)) 
               , (λ {x} → subst (_>_ x)) 
    } 
  }
  where
    _>_ : Bool → Bool → Set
    x > y = y < x

    transitive : {x y z : Bool} → x < y → y < z → x < z
    transitive F<T ()

    compare : (x y : Bool) → Tri (x < y) (x ≡ y) (x > y)
    compare true  true  = tri≈ (λ ()) refl   (λ ())
    compare true  false = tri> (λ ()) (λ ()) F<T
    compare false true  = tri< F<T    (λ ()) (λ ())
    compare false false = tri≈ (λ ()) refl   (λ ())