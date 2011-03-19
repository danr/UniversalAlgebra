{-# OPTIONS --universe-polymorphism #-}
module StackedMonoids.StackedMonoid where

open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Relation.Binary
open import Level

import Algebra.FunctionProperties as FP

open FP using (Op₂)

record StackedMonoid c ℓ (n : ℕ) : Set (suc (c ⊔ ℓ)) where
  field
    universe : Setoid c ℓ
  
  open Setoid universe renaming (Carrier to X ; _≈_ to ≈)
  open FP ≈

  field
    id       : Fin n → X 
    op       : Fin n → Op₂ X 
    assoc    : (x : Fin n) → Associative (op x) 
    identity : (x : Fin n) → Identity (id x) (op x)
    cong     : (x : Fin n) → (op x) Preserves₂ ≈ ⟶ ≈ ⟶ ≈ 

  open Setoid universe public renaming (Carrier to X)

open import Data.Vec 
open import Data.ParallelVector
open import Data.Product hiding (map ; zip)
open import Function
open import Relation.Binary.PropositionalEquality

module Interpret (n : ℕ) where
  
  ⟦_⟧ : ∀ {i} → Set i → Set i
  ⟦ X ⟧ = Vec X n

  ⟦_⟧′ : ∀ {i j} {X : Set i} → (X → Set j) → Vec X n → Set (i ⊔ j)
  ⟦ B ⟧′ xs = ParVec B xs 

  ⟦_⟧″ : ∀ {i j} {X Y : Set i} → (X → Y → Set j) → Vec X n → Vec Y n → Set (i ⊔ j)
  ⟦ B ⟧″ xs ys = ParVec (uncurry B) (zip xs ys)

  proj₁-zip : ∀ {i j} {A : Set i} {B : Set j} {n : ℕ}
            → (x : Fin n) (xs : Vec A n) (ys : Vec B n)
            → proj₁ (lookup x (zip xs ys)) ≡ lookup x xs
  proj₁-zip zero    (x ∷ xs) (y ∷ ys) = refl
  proj₁-zip (suc n) (x ∷ xs) (y ∷ ys) = proj₁-zip n xs ys

  proj₂-zip : ∀ {i j} {A : Set i} {B : Set j} {n : ℕ}
            → (x : Fin n) (xs : Vec A n) (ys : Vec B n)
            → proj₂ (lookup x (zip xs ys)) ≡ lookup x ys
  proj₂-zip zero    (x ∷ xs) (y ∷ ys) = refl
  proj₂-zip (suc n) (x ∷ xs) (y ∷ ys) = proj₂-zip n xs ys

-- One way of instantiating a stacked monoid without using the Fin-indexed functions
stackMonoid : ∀ {c ℓ} (n : ℕ) (universe : Setoid c ℓ)
            → let open Setoid universe renaming (Carrier to X ; _≈_ to ≈)
                  open FP ≈
                  open Interpret n
              in (ε : ⟦ X ⟧) (∙ : ⟦ Op₂ X ⟧) 
               → ⟦ Associative ⟧′ ∙ 
               → ⟦ Identity ⟧″ ε ∙
               → ⟦ (λ ⋆ → ⋆ Preserves₂ ≈ ⟶ ≈ ⟶ ≈) ⟧′ ∙ 
               → StackedMonoid c ℓ n
stackMonoid n u ε ∙ assocs identities congs = record 
  { universe = u
  ; id       = flip lookup ε
  ; op       = flip lookup ∙
  ; assoc    = par-lookup assocs
  ; identity = λ x → subst₂ Identity (proj₁-zip x ε ∙) (proj₂-zip x ε ∙) (par-lookup identities x)
  ; cong     = par-lookup congs 
  }
  where
    open Setoid u
    open FP _≈_
    open Interpret n

open import Algebra.Structures

fromMonoids : ∀ {c ℓ} {X : Set c} {_≈_ : Rel X ℓ} {n : ℕ}
            → let open Interpret (suc n)
              in (ε : ⟦ X ⟧) (∙ : ⟦ Op₂ X ⟧)
               → ⟦ IsMonoid _≈_ ⟧″ ∙ ε
               → StackedMonoid c ℓ (suc n)
fromMonoids {X = X} {_≈_} {n} ε ∙ ms = record 
  { universe = {!head ms!}
  ; id       = {!!}
  ; op       = {!!}
  ; assoc    = {!!}
  ; identity = {!!}
  ; cong     = {!!}
  }
  where
    open FP _≈_
    open Interpret n 