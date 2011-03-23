{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.Lemmas {β₁ β₂} (BA : BooleanAlgebra β₁ β₂) where

open BooleanAlgebra BA renaming (Carrier to X)
import Algebra.Props.BooleanAlgebra as P-BA; open P-BA BA

private
  module C = CommutativeSemiring ∨-∧-commutativeSemiring 
    renaming (+-identity to ∨-identity ; *-identity to ∧-identity) 

import Relation.Binary.EqReasoning as EqR; open EqR setoid

open import Function
open import Data.Product

postulate ⁇ : ∀ {x y} → x ≈ y

lem₁ : ∀ x y z → x ∧ y ∧ z ≈ (x ∧ y) ∧ x ∧ z
lem₁ x y z = begin
    x ∧ (y ∧ z)          ≈⟨ sym (∧-idempotent x) ⟨ ∧-cong ⟩ refl {y ∧ z} ⟩
    (x ∧ x) ∧ (y ∧ z)    ≈⟨ sym (∧-assoc (x ∧ x) y z) ⟩
    ((x ∧ x) ∧ y) ∧ z    ≈⟨ (∧-assoc x x y) ⟨ ∧-cong ⟩ refl {z} ⟩
    (x ∧ (x ∧ y)) ∧ z    ≈⟨ refl {x} ⟨ ∧-cong ⟩ ∧-comm x y ⟨ ∧-cong ⟩ refl {z} ⟩
    (x ∧ (y ∧ x)) ∧ z    ≈⟨ sym (∧-assoc x y x) ⟨ ∧-cong ⟩ refl {z} ⟩
    ((x ∧ y) ∧ x) ∧ z    ≈⟨ ∧-assoc (x ∧ y) x z  ⟩
    (x ∧ y) ∧ (x ∧ z)
  ∎

lem₂ : ∀ x y z → y ∧ z ≈ (x ∧ y) ∧ ¬ x ∧ z
lem₂ x y z = ⁇ {- begin
    y ∧ z                   ≈⟨ {!proj₁ ∧-complement x!} ⟩
    {!!}                    ≈⟨ {!!} ⟩
    (x ∧ y) ∧ ¬ x ∧ z             
  ∎
-}

lem₃ : ∀ x y z → y ∧ z ≈ (¬ x ∧ y) ∧ x ∧ z
lem₃ x y z = ⁇ {- begin
    {!!}                    ≈⟨ {!!} ⟩
    {!!}                    ≈⟨ {!!} ⟩
    {!!}             
  ∎
-}

lem₄ : ∀ x y z → x ∧ y ∧ z ≈ y ∧ x ∧ z
lem₄ x y z = ⁇ {- begin
    {!!}                    ≈⟨ {!!} ⟩
    {!!}                    ≈⟨ {!!} ⟩
    {!!}             
  ∎
-}
