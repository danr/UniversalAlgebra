{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.Lemmas {β₁ β₂} (BA : BooleanAlgebra β₁ β₂) where

open BooleanAlgebra BA renaming (Carrier to X)
import Algebra.Props.BooleanAlgebra as P-BA; open P-BA BA public

module C = CommutativeSemiring ∨-∧-commutativeSemiring 
  renaming (+-identity to ∨-identity ; *-identity to ∧-identity) 

import Relation.Binary.EqReasoning as EqR; open EqR setoid

open import Function
open import Data.Product

lemma₁ : ∀ {α β γ δ} → (α ∧ β) ∧ (γ ∧ δ) 
                     ≈ (α ∧ γ) ∧ (β ∧ δ)
lemma₁ {α} {β} {γ} {δ} = begin
    (α ∧ β) ∧ (γ ∧ δ) ≈⟨ ∧-assoc α β (γ ∧ δ) ⟩
    α ∧ (β ∧ (γ ∧ δ)) ≈⟨ refl {α} ⟨ ∧-cong ⟩ sym (∧-assoc β γ δ) ⟩
    α ∧ ((β ∧ γ) ∧ δ) ≈⟨ refl {α} ⟨ ∧-cong ⟩ (∧-comm β γ ⟨ ∧-cong ⟩ refl {δ}) ⟩
    α ∧ ((γ ∧ β) ∧ δ) ≈⟨ refl {α} ⟨ ∧-cong ⟩ ∧-assoc γ β δ ⟩
    α ∧ (γ ∧ (β ∧ δ)) ≈⟨ sym (∧-assoc α γ (β ∧ δ)) ⟩
    (α ∧ γ) ∧ (β ∧ δ)
  ∎

lemma₂ : ∀ {α β γ δ} → ⊥ ≈ α ∧ β 
                     → ⊥ ≈ (γ ∧ α) ∧ (δ ∧ β)
lemma₂ {α} {β} {γ} {δ} eq = begin
    ⊥                    ≈⟨ sym (proj₁ C.zero (γ ∧ δ)) ⟩
    ⊥ ∧ (γ ∧ δ)          ≈⟨ eq ⟨ ∧-cong ⟩ refl {γ ∧ δ} ⟩
    (α ∧ β) ∧ (γ ∧ δ)    ≈⟨ lemma₁ ⟩
    (α ∧ γ) ∧ (β ∧ δ)    ≈⟨ ∧-comm α γ ⟨ ∧-cong ⟩ ∧-comm β δ ⟩
    (γ ∧ α) ∧ (δ ∧ β)
  ∎

lemma₃ : ∀ {α β γ δ} → ⊥ ≈ γ ∧ δ → ⊥ ≈ (γ ∧ α) ∧ (δ ∧ β)
lemma₃ {α} {β} {γ} {δ} eq = begin
    ⊥                 ≈⟨ lemma₂ eq ⟩
    (α ∧ γ) ∧ (β ∧ δ) ≈⟨ ∧-comm α γ ⟨ ∧-cong ⟩ ∧-comm β δ ⟩
    (γ ∧ α) ∧ (δ ∧ β)
  ∎

