{-# OPTIONS --universe-polymorphism #-}
module Data.ParallelList where

open import Data.Product
open import Data.ParallelVector
open import Data.List renaming (_++_ to _++′_)
open import Data.Vec hiding (_++_)
open import Level

infixr 5 _∷_

data ParList {i} {j} {A : Set i} (B : A → Set j) : List A → Set (i ⊔ j) where
  []  : ParList B []
  _∷_ : ∀ {x} {xs} (p : B x) (ps : ParList B xs) → ParList B (x ∷ xs)

module PL {i} {j} {A : Set i} {B : A → Set j} where

  fromParList : {xs : List A} → ParList B xs → ParVec B (fromList xs) 
  fromParList [] = []
  fromParList (p ∷ ps) = p ∷ fromParList ps

  toFlatList : {xs : List A} → ParList B xs → List (∃ B) 
  toFlatList []       = []
  toFlatList (p ∷ ps) = (, p) ∷ (toFlatList ps)

  infixr 5 _++_

  _++_ : {xs ys : List A} → ParList B xs → ParList B ys → ParList B (xs ++′ ys)
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
  []       ++ ys = ys

open PL public



