module FreeMonoid (A : Set) where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Algebra renaming (Monoid to Monoid′)
open import Algebra.Morphism
open import Data.List renaming (monoid to ListMonoid)
open import Data.Product using (proj₁ ; proj₂)
open import Level

-- No universe polymorphism here 
Monoid : Set₁
Monoid = Monoid′ zero zero

-- The underlying set of a monoid
∣_∣ : Monoid → Set
∣_∣ = Monoid.Carrier

-- Definition of a monoid homomorphism
record _-Mon→_ (M : Monoid) (N : Monoid) : Set₁ where
  private
    module M = Monoid M
    module N = Monoid N
  open Definitions (∣ M ∣) (∣ N ∣) N._≈_

  field 
    ⟦_⟧     : Morphism
    ⟦⟧-cong : ⟦_⟧ Preserves M._≈_ ⟶ N._≈_
    ε-homo  : Homomorphic₀ ⟦_⟧ M.ε N.ε
    ∙-homo  : Homomorphic₂ ⟦_⟧ M._∙_ N._∙_

-- The underlying function of a monoid homomorphism
⟦_⟧′ : {M N : Monoid} → M -Mon→ N → ∣ M ∣ → ∣ N ∣
⟦_⟧′ = _-Mon→_.⟦_⟧
  
--
-- In Mon:
--
--        Φ
--  [A] ……………→ M
--
-- In Sets:
--
--       φ
--  [A] ----→ M
--   ↑      ↗ 
--   |     /
-- i |    /
--   |   / f
--   |  / 
--   A
--

-- Insertion of generators

i : A → List A
i x = [ x ]

-- List A with i has the UMP of the free monoid

module Universal (M : Monoid) (f : A → ∣ M ∣) where

  -- Given a monoid M, and a function from A to its underlying set,
  -- there is a monoid homomorphism Φ from List A (as a monoid) to M.

  open Monoid M renaming (refl to M-refl ; sym to M-sym ; trans to M-trans)

  -- The underlying function on the homomorphism
  φ : List A → ∣ M ∣
  φ [] = ε
  φ (x ∷ xs) = f x ∙ φ xs

  -- The homomorphism
  Φ : ListMonoid A -Mon→ M
  Φ = record 
    { ⟦_⟧ = φ
    ; ⟦⟧-cong = φ-cong
    ; ε-homo = M-refl
    ; ∙-homo = ∙-homo
    }
    where
      φ-cong : {xs ys : List A} → xs ≡ ys → φ xs ≈ φ ys
      φ-cong refl = M-refl

      ∙-homo : (xs ys : List A) → φ (xs ++ ys) ≈ φ xs ∙ φ ys
      ∙-homo [] ys = M-sym (proj₁ identity (φ ys))
      ∙-homo (x ∷ xs) ys = M-trans (∙-cong (M-refl {f x}) (∙-homo xs ys)) 
                                 (M-sym (assoc (f x) (φ xs) (φ ys))) 

  -- Equal on singleton lists:
  singletons : (a : A) → φ [ a ] ≈ f a
  singletons a = proj₂ identity (f a)

  -- Futhermore, this monoid homomorphism is unique: given any other 
  -- monoid homomorphism γ that is also equal on singleton lists, 
  -- then the underlying functions of γ and Φ are equal on all elements.
  module Unique (γ : ListMonoid A -Mon→ M) 
                (eq : (a : A) → ⟦ γ ⟧′ [ a ] ≈ φ [ a ]) where

    open _-Mon→_ γ

    unique : (xs : List A) → ⟦ γ ⟧′ xs ≈ φ xs
    unique [] = ε-homo 
    unique (x ∷ xs) = M-trans (∙-homo [ x ] xs) 
                       (M-trans (∙-cong (eq x) (unique xs)) 
                       (∙-cong (proj₂ identity (f x)) (M-refl {φ xs})))

