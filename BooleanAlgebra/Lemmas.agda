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

lemma₄ : ∀ {x y z} → x ∨ y ≈ x → (z ∧ x) ∨ (z ∧ y) ≈ z ∧ x
lemma₄ {x} {y} {z} eq = begin
    (z ∧ x) ∨ (z ∧ y)    ≈⟨ sym (proj₁ ∧-∨-distrib z x y) ⟩
    z ∧ (x ∨ y)          ≈⟨ refl ⟨ ∧-cong ⟩ eq ⟩
    z ∧ x
  ∎

private
  helper-lemma₅ : ∀ {x y z} → x ∨ y ≈ x → x ∨ (z ∧ y) ≈ x
  helper-lemma₅ {x} {y} {z} eq = begin
      x ∨ (z ∧ y)          ≈⟨ proj₁ ∨-∧-distrib x z y ⟩
      (x ∨ z) ∧ (x ∨ y)    ≈⟨ refl ⟨ ∧-cong ⟩ eq ⟩
      (x ∨ z) ∧ x          ≈⟨ ∧-comm _ _  ⟩
      x ∧ (x ∨ z)          ≈⟨ proj₂ absorptive x z ⟩
      x
    ∎
  
lemma₅ : ∀ {x y z} → x ∨ y ≈ x → (⊤ ∧ x) ∨ (z ∧ y) ≈ ⊤ ∧ x
lemma₅ {x} {y} {z} eq = begin
    (⊤ ∧ x) ∨ (z ∧ y) ≈⟨ proj₁ C.∧-identity x ⟨ ∨-cong ⟩ refl ⟩     
    x ∨ (z ∧ y)       ≈⟨ helper-lemma₅ eq ⟩
    x                 ≈⟨ sym (proj₁ C.∧-identity x) ⟩
    ⊤ ∧ x
  ∎

lemma₆ : ∀ {x y z} → x ∨ y ∨ z ≈ y ∨ x ∨ z
lemma₆ {x} {y} {z} = begin
    x ∨ y ∨ z       ≈⟨ sym (∨-assoc x y z) ⟩ 
    (x ∨ y) ∨ z     ≈⟨ ∨-comm x y ⟨ ∨-cong ⟩ refl ⟩ 
    (y ∨ x) ∨ z     ≈⟨ ∨-assoc y x z ⟩ 
    y ∨ x ∨ z
  ∎



{-
begin
    ?                 ≈⟨ ? ⟩
    ?                 ≈⟨ ? ⟩
    ?                 ≈⟨ ? ⟩
    ?                 ≈⟨ ? ⟩
    ?
  ∎
-}