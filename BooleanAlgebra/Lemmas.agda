{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.Lemmas {β₁ β₂} (BA : BooleanAlgebra β₁ β₂) where

open BooleanAlgebra BA 

-- Todo!!

postulate ⁇ : ∀ {x y} → x ≈ y

lem₁ : ∀ x y z → x ∧ y ∧ z ≈ (x ∧ y) ∧ x ∧ z
lem₁ x y z = ⁇

lem₂ : ∀ x y z → y ∧ z ≈ (x ∧ y) ∧ ¬ x ∧ z
lem₂ x y z = ⁇

lem₃ : ∀ x y z → y ∧ z ≈ (¬ x ∧ y) ∧ x ∧ z
lem₃ x y z = ⁇

lem₄ : ∀ x y z → x ∧ y ∧ z ≈ y ∧ x ∧ z
lem₄ x y z = ⁇
