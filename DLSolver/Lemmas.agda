{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module DLSolver.Lemmas {δ₁ δ₂} (DL : DistributiveLattice δ₁ δ₂) where

------------------------------------------------------------------------
-- Some lemmas used in the solver, also reexports the properties
-- from Algebra.Props.DistributiveLattice

open DistributiveLattice DL renaming (Carrier to X)
import Algebra.Props.DistributiveLattice as P-DL; open P-DL DL public

import Relation.Binary.EqReasoning as EqR; open EqR setoid

open import Function
open import Data.Product

------------------------------------------------------------------------
-- Lemmas used in DNF-Correct
lemma₀ : ∀ {x y} → x ∧ y ≈ x ∧ x ∧ y
lemma₀ {x} {y} = begin
    x ∧ y                ≈⟨ sym (∧-idempotent x) ⟨ ∧-cong ⟩ refl ⟩
    (x ∧ x) ∧ y          ≈⟨ ∧-assoc x x y ⟩
    x ∧ x ∧ y
  ∎

lemma₁ : ∀ {a b c d} → a ≈ b ∧ c → d ∧ a ≈ b ∧ d ∧ c
lemma₁ {a} {b} {c} {d} eq = begin
    d ∧ a                ≈⟨ refl ⟨ ∧-cong ⟩ eq ⟩
    d ∧ b ∧ c            ≈⟨ sym (∧-assoc d b c) ⟩
    (d ∧ b) ∧ c          ≈⟨ ∧-comm d b ⟨ ∧-cong ⟩ refl ⟩
    (b ∧ d) ∧ c          ≈⟨ ∧-assoc b d c ⟩
    b ∧ d ∧ c
  ∎

lemma₂ : ∀ {a b c d} → a ≈ b ∧ c → d ∧ a ≈ (d ∧ b) ∧ d ∧ c
lemma₂ {a} {b} {c} {d} eq = begin
    d ∧ a                ≈⟨ lemma₀ ⟩
    d ∧ (d ∧ a)          ≈⟨ refl ⟨ ∧-cong ⟩  lemma₁ eq ⟩
    d ∧ (b ∧ (d ∧ c))    ≈⟨ refl ⟨ ∧-cong ⟩ sym (∧-assoc b d c) ⟩
    d ∧ ((b ∧ d) ∧ c)    ≈⟨ sym (∧-assoc d (b ∧ d) c) ⟩
    (d ∧ (b ∧ d)) ∧ c    ≈⟨ sym (∧-assoc _ _ _) ⟨ ∧-cong ⟩ refl  ⟩
    ((d ∧ b) ∧ d) ∧ c    ≈⟨ ∧-assoc (d ∧ b) d c ⟩
    (d ∧ b) ∧ (d ∧ c)
  ∎

lemma₃ : ∀ {x y} → x ∧ y ≈ (x ∧ y) ∧ x
lemma₃ {x} {y} = begin
    x ∧ y                ≈⟨ sym (∧-idempotent x) ⟨ ∧-cong ⟩ refl ⟩
    (x ∧ x) ∧ y          ≈⟨ ∧-assoc x x y ⟩
    x ∧ x ∧ y            ≈⟨ refl ⟨ ∧-cong ⟩ ∧-comm x y ⟩
    x ∧ y ∧ x            ≈⟨ sym (∧-assoc x y x) ⟩
    (x ∧ y) ∧ x
  ∎

------------------------------------------------------------------------
-- Lemmas used in Redundancies
lemma₄ : ∀ {x y z} → x ∨ y ≈ x → (z ∧ x) ∨ (z ∧ y) ≈ z ∧ x
lemma₄ {x} {y} {z} eq = begin
    (z ∧ x) ∨ (z ∧ y)    ≈⟨ sym (proj₁ ∧-∨-distrib z x y) ⟩
    z ∧ (x ∨ y)          ≈⟨ refl ⟨ ∧-cong ⟩ eq ⟩
    z ∧ x
  ∎

lemma₅ : ∀ {x y z} → x ∨ y ≈ x → x ∨ (z ∧ y) ≈ x
lemma₅ {x} {y} {z} eq = begin
    x ∨ (z ∧ y)       ≈⟨ proj₁ ∨-∧-distrib x z y ⟩
    (x ∨ z) ∧ (x ∨ y) ≈⟨ ∧-cong refl eq ⟩
    (x ∨ z) ∧ x       ≈⟨ ∧-comm _ _ ⟩
    x ∧ (x ∨ z)       ≈⟨ proj₂ absorptive x z ⟩
    x
  ∎

------------------------------------------------------------------------
-- Lemma used in Redundancies and DNF-Sort
lemma₆ : ∀ {x y z} → x ∨ y ∨ z ≈ y ∨ x ∨ z
lemma₆ {x} {y} {z} = begin
    x ∨ y ∨ z       ≈⟨ sym (∨-assoc x y z) ⟩ 
    (x ∨ y) ∨ z     ≈⟨ ∨-comm x y ⟨ ∨-cong ⟩ refl ⟩ 
    (y ∨ x) ∨ z     ≈⟨ ∨-assoc y x z ⟩ 
    y ∨ x ∨ z
  ∎
