{-# OPTIONS --universe-polymorphism #-}
module Data.ParallelList where

open import Data.Product
open import Data.ParallelVector
open import Data.List
open import Data.Vec
open import Level

data ParList {i} {j} {A : Set i} (B : A → Set j) : List A → Set (i ⊔ j) where
  []  : ParList B []
  _∷_ : ∀ {x} {xs} (p : B x) (ps : ParList B xs) → ParList B (x ∷ xs)

fromParList : ∀ {i} {j} {A : Set i} {B : A → Set j} {xs : List A} → ParList B xs → ParVec B (fromList xs) 
fromParList [] = []
fromParList (p ∷ ps) = p ∷ fromParList ps

toFlatList : ∀ {i} {j} {A : Set i} {B : A → Set j} {xs : List A} → ParList B xs → List (∃ B) 
toFlatList []       = []
toFlatList (p ∷ ps) = (, p) ∷ (toFlatList ps)

toFlatVec : ∀ {i} {j} {A : Set i} {B : A → Set j} {xs : List A} → ParList B xs → Vec (∃ B) (length xs)
toFlatVec []       = []
toFlatVec (p ∷ ps) = (, p) ∷ (toFlatVec ps)
