--------------------------------------------------------------------------------
-- Some work based on a lecture notes in an AFP by Nils Anders Danielsson:
-- http://www.cse.chalmers.se/edu/course/afp/lectures/lecture11/html/Proof-by-reflection.html
--
-- To do : Better representation of the normal form to avoid the use of ↔
-- Idea : Sort by Fins?
--------------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module Reflection.AbelianGroup {c ℓ} (Gr : AbelianGroup c ℓ) where

open AbelianGroup Gr renaming (Carrier to G)
import Algebra.Props.Group as GP; open GP (group)
import Algebra.Props.AbelianGroup as AP; open AP (Gr)

open import Data.Vec hiding (_⊛_ ; _++_ ; [_] ; map)
open import Data.List 
open import Data.Bool 
open import Data.Nat 
open import Data.Fin 
open import Data.Product renaming (map to _⋆_)

open import Function

second : ∀ {i j} {A : Set i} {B : A → Set j} {C : A → Set j} 
       → (∀ {x} → B x → C x) → Σ A B → Σ A C
second f = id ⋆ f

open import Relation.Nullary.Decidable hiding (map)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality 
  renaming (trans to ≡-trans ; sym to ≡-sym ; refl to ≡-refl 
           ; isEquivalence to ≡-isEquivalence)

--------------------------------------------------------------------------------
-- Modelling an expression of groups

data Expr (n : ℕ) : Set where
  var     : (x : Fin n) → Expr n
  unit    : Expr n
  inv     : (e : Expr n) → Expr n
  _⊛_ _↔_ : (e₁ e₂ : Expr n) → Expr n

--------------------------------------------------------------------------------
-- Evaluating an expression under a context

Env : ℕ → Set c
Env n = Vec G n

⟦_⟧ : ∀ {n} → Expr n → Env n → G
⟦ var x   ⟧ Γ = lookup x Γ
⟦ unit    ⟧ Γ = ε
⟦ inv e   ⟧ Γ = ⟦ e ⟧ Γ ⁻¹
⟦ e₁ ⊛ e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ ∙ ⟦ e₂ ⟧ Γ
⟦ e₁ ↔ e₂ ⟧ Γ = ⟦ e₂ ⟧ Γ ∙ ⟦ e₁ ⟧ Γ

--------------------------------------------------------------------------------
-- A normal form, a linearisation so to say, of an expression

Normal : ℕ → Set
Normal n = List (Fin n × Bool)

⟦_⟧′ : ∀ {n} → Normal n → Env n → G
⟦_⟧′ []                 Γ = ε
⟦_⟧′ ((x , true)  ∷ xs) Γ = lookup x Γ ⁻¹ ∙ ⟦ xs ⟧′ Γ
⟦_⟧′ ((x , false) ∷ xs) Γ = lookup x Γ    ∙ ⟦ xs ⟧′ Γ

--------------------------------------------------------------------------------
-- Compute the normal form of an expression

normalise : ∀ {n} → Expr n → Normal n
normalise (var x)   = [ ( x , false ) ]
normalise unit      = []
normalise (inv e)   = map (second not) (normalise e)
normalise (e₁ ⊛ e₂) = normalise e₁ ++ normalise e₂ 
normalise (e₁ ↔ e₂) = normalise e₁ ++ normalise e₂

--------------------------------------------------------------------------------
-- This is a homomorphism under _++_ of normal forms and _∙_ in the group

homomorphic : ∀ {n} (nf₁ nf₂ : Normal n) (Γ : Env n)
            → ⟦ nf₁ ++ nf₂ ⟧′ Γ ≈ ⟦ nf₁ ⟧′ Γ ∙ ⟦ nf₂ ⟧′ Γ
homomorphic []                  nf₂ Γ = sym (proj₁ identity (⟦ nf₂ ⟧′ Γ))
homomorphic ((x , true)  ∷ nf₁) nf₂ Γ = trans (⁻¹-cong refl ⟨ ∙-cong ⟩ homomorphic nf₁ nf₂ Γ) 
                                              (sym (assoc (lookup x Γ ⁻¹) (⟦ nf₁ ⟧′ Γ) (⟦ nf₂ ⟧′ Γ)))  
homomorphic ((x , false) ∷ nf₁) nf₂ Γ = trans (refl ⟨ ∙-cong ⟩ (homomorphic nf₁ nf₂ Γ)) 
                                              (sym (assoc (lookup x Γ) (⟦ nf₁ ⟧′ Γ) (⟦ nf₂ ⟧′ Γ)))

--------------------------------------------------------------------------------
-- Inverting the normal form and then evaluating, is the same as inverting after

invertible : ∀ {n} (nf : Normal n) (Γ : Env n) 
           → ⟦ map (second not) nf ⟧′ Γ ≈ ⟦ nf ⟧′ Γ ⁻¹
invertible []                 Γ = trans (sym (proj₂ inverse ε)) (proj₁ identity (ε ⁻¹))
invertible ((x , true)  ∷ nf) Γ = trans (refl ⟨ ∙-cong ⟩ invertible nf Γ) 
                                 (trans (sym (⁻¹-involutive (lookup x Γ)) ⟨ ∙-cong ⟩ refl)
                                        (-‿∙-comm (lookup x Γ ⁻¹) (⟦ nf ⟧′ Γ)))
invertible ((x , false) ∷ nf) Γ = trans (⁻¹-cong refl ⟨ ∙-cong ⟩ invertible nf Γ) 
                                        (-‿∙-comm (lookup x Γ) (⟦ nf ⟧′ Γ))

--------------------------------------------------------------------------------
-- Normalisation of an expression respects evaluation of the expression

normalise-correct : ∀ {n} (e : Expr n) (Γ : Env n) 
                  → ⟦ normalise e ⟧′ Γ ≈ ⟦ e ⟧ Γ
normalise-correct (var x)   Γ = proj₂ identity (lookup x Γ) 
normalise-correct unit      Γ = refl
normalise-correct (inv e)   Γ = trans (invertible (normalise e) Γ) (⁻¹-cong (normalise-correct e Γ))
normalise-correct (e₁ ⊛ e₂) Γ = trans (homomorphic (normalise e₁) (normalise e₂) Γ)
                                      (normalise-correct e₁ Γ ⟨ ∙-cong ⟩ normalise-correct e₂ Γ)
normalise-correct (e₁ ↔ e₂) Γ = trans (homomorphic (normalise e₁) (normalise e₂) Γ)
                              ( trans (normalise-correct e₁ Γ ⟨ ∙-cong ⟩ normalise-correct e₂ Γ)
                                      (comm (⟦ e₁ ⟧ Γ) (⟦ e₂ ⟧ Γ)))

--------------------------------------------------------------------------------
-- Using the fancy Reflection library

import Relation.Binary.Reflection as Reflection
open import Relation.Binary

Group-Setoid : Setoid c ℓ
Group-Setoid = record { Carrier = G ; _≈_ = _≈_ ; isEquivalence = isEquivalence }

open Reflection Group-Setoid var ⟦_⟧ (λ e Γ → ⟦ normalise e ⟧′ Γ) normalise-correct
  public renaming (prove to prove′ ; _⊜_ to _:=_)

--------------------------------------------------------------------------------
-- Some examples

module Reflection-Examples (x y z : G) where
  
  ex₁ : x ∙ (y ∙ (z ∙ z)) ≈ ((x ∙ y) ∙ ε) ∙ (z ∙ z)
  ex₁ = solve₁ 3 (λ x y z → x ⊛ (y ⊛ (z ⊛ z)) := ((x ⊛ y) ⊛ unit) ⊛ (z ⊛ z)) x y z refl 

  ex₂ : (x ∙ y) ⁻¹ ≈ y ⁻¹ ∙ x ⁻¹
  ex₂ = solve₁ 2 (λ x y → inv (x ⊛ y) := inv x ↔ inv y) x y refl

  ex₃  : ε ⁻¹ ≈ ε
  ex₃ = solve₁ 0 (inv unit := unit) refl
