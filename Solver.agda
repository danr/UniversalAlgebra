-- A solver for stacked monoids
-- Work in progress!!

{-# OPTIONS --universe-polymorphism #-}
module Solver where

open import Data.Bool renaming (_≟_ to _≟-Bool_)
open import Data.List renaming (_++_ to _++_ ; zip to List-zip ; map to List-map)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)
open import Function renaming (id to I)
open import Data.Nat hiding (_⊔_ ; _≟_)
open import Data.Empty

module NodeDecoratedListTree (A N : Set) where
 
  data NLT : Set where
    leaf   : (x : A) → NLT
    branch : (n : N) (t : List NLT) → NLT

open NodeDecoratedListTree public
  
module Operations {A N : Set} {_≟_ : Decidable (_≡_ {A = N})} where

    _≟_then_else_ : ∀ {A : Set} → N → N → A → A → A
    n ≟ n′ then x else y = if ⌊ n ≟ n′ ⌋ then x else y

  
    _++_⟨_⟩ : NLT A N → NLT A N → N → NLT A N
    leaf x     ++ leaf x′      ⟨ n₀ ⟩ = branch n₀ (leaf x ∷ leaf x′ ∷ [])
    leaf x     ++ branch n t   ⟨ n₀ ⟩ = n₀ ≟ n then branch n (leaf x ∷ t) 
                                               else branch n₀ (leaf x ∷ branch n t ∷ [])
    branch n t ++ leaf x       ⟨ n₀ ⟩ = n₀ ≟ n then branch n (t ++ [ leaf x ])
                                               else branch n₀ (branch n t ∷ leaf x ∷ [])
    branch n t ++ branch n′ t′ ⟨ n₀ ⟩ = 
      n₀ ≟ n then (n₀ ≟ n′ then branch n (t ++ t′) 
                           else branch n (t ++ [ branch n′ t′ ])) 
             else (n₀ ≟ n′ then branch n′ ([ branch n t ] ++ t′) 
                           else branch n₀ (branch n t ∷ branch n′ t′ ∷ []))

import Algebra.FunctionProperties as FP
open import Data.ParallelList
open import Data.ParallelVector
open import Data.Vec hiding (foldr)
open import Level
open import Data.Product renaming (zip to Pzip)
open import Data.Fin
open import Data.Fin.Props

abstract
  _!_ : ∀ {i} {A : Set i} {n : ℕ} → Vec A n → Fin n → A
  xs ! n = lookup n xs

                     -- How many stacked monoids
module N-Monoid-Solver (n : ℕ) where

  -- Should be called N-Monoid, but right now only m for short so you can see the goals a little better
  record m c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      universe : Setoid c ℓ
    
    open Setoid universe renaming (Carrier to X ; _≈_ to ≈)
    open FP ≈
  
    field
      id       : Fin n → X 
      op       : Fin n → Op₂ X 
      assocs   : (x : Fin n) → Associative (op x) 
      identity : (x : Fin n) → Identity (id x) (op x)
      congs    : (x : Fin n) → (op x) Preserves₂ ≈ ⟶ ≈ ⟶ ≈ 

    open Setoid universe public renaming (Carrier to X)

  module Solver (N : m zero zero) {v : ℕ} where  -- Number of free variables

    open m N public   


    open Operations {Fin v} {Fin n} {_≟_}

    -- Standard procedure

    data Expr : Set where
      var : (x : Fin v) → Expr
      ε   : (x : Fin n) → Expr
      _[_]_ : (e₁ : Expr) (∙ : Fin n) (e₂ : Expr) → Expr

    Env : Set
    Env = Vec X v

    ⟦_⟧ : Expr → Env → X
    ⟦ var x       ⟧ Γ = lookup x Γ
    ⟦ ε n         ⟧ Γ = id n 
    ⟦ e₁ [ ∙ ] e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ ⟨ op ∙ ⟩ ⟦ e₂ ⟧ Γ

    Normal : Set
    Normal = NLT (Fin v) (Fin n)

    mutual
      ⟦_⟧″ : List Normal → Env → List X
      ⟦ []     ⟧″ Γ = []
      ⟦ x ∷ xs ⟧″ Γ = ⟦ x ⟧′ Γ ∷ ⟦ xs ⟧″ Γ

      ⟦_⟧′ : Normal → Env → X
      ⟦ leaf x     ⟧′ Γ = lookup x Γ
      ⟦ branch n t ⟧′ Γ = foldr (op n) (id n) (⟦ t ⟧″ Γ)

    normalise : Expr → Normal
    normalise (var x)       = leaf x
    normalise (ε x)         = branch x []
    normalise (e₁ [ ∙ ] e₂) = (normalise e₁) ++ (normalise e₂) ⟨ ∙ ⟩

    homomorphic : (∙ : Fin n) (nf₁ nf₂ : Normal) (Γ : Env) 
                → ⟦ nf₁ ++ nf₂ ⟨ ∙ ⟩ ⟧′ Γ ≈ (⟦ nf₁ ⟧′ Γ ⟨ op ∙ ⟩ ⟦ nf₂ ⟧′ Γ)
    homomorphic ∙ (leaf x) (leaf x') Γ = congs ∙ refl (proj₂ (identity ∙) (lookup x' Γ))
    homomorphic ∙ (leaf x) (branch n′ t) Γ with ∙ ≟ n′
    ... | yes p rewrite p = refl 
    ... | no ¬p = congs ∙ refl (proj₂ (identity ∙) _)
    homomorphic ∙ (branch n′ t) (leaf x) Γ with ∙ ≟ n′
    ... | yes p rewrite p = {!!}   -- need foldr lemmas
    ... | no ¬p = congs ∙ refl (proj₂ (identity ∙) (lookup x Γ))
    homomorphic ∙ (branch n′ t′) (branch n″ t″) Γ with ∙ ≟ n′ | ∙ ≟ n″
    ... | yes p | yes p′ rewrite p | p′ = {!!}          -- will need assoc here
    ... | yes p | no ¬p′ rewrite p = {!!}   -- foldr xs ++ [ y ] lemma?
    ... | no ¬p | yes p′ rewrite p′ = refl
    ... | no ¬p | no ¬p′ = congs ∙ refl (proj₂ (identity ∙) _) 

    correct : (e : Expr) (Γ : Env) → ⟦ normalise e ⟧′ Γ ≈ ⟦ e ⟧ Γ
    correct (var x)       Γ = refl
    correct (ε x)         Γ = refl
    correct (e₁ [ ∙ ] e₂) Γ = trans (homomorphic ∙ (normalise e₁) (normalise e₂) Γ) 
                                    (congs ∙ (correct e₁ Γ) (correct e₂ Γ))


-- Ideas:
-- Enhance the NLT structure to parameterize over if the lists can be empty 
-- This will correspond to identitites
-- Also lists can be replaced to binary trees if the structure is not associative
-- Commutativity seems in general to be hard,
-- whereas associativity+commutativity is a multiset
-- where 
-- ∙ 1 or more elements if no identities
-- ∙ 0 or more elmenets if identities
-- ∙ ℤ if inverses
-- ∙ abs max 1 if idempotent? (hmm)
--
-- However, it is not straightforward to represent bags/multisets.
--
-- Finally, what happens when we add distributivity and absorption?
-- These are the most interesting laws: they allow ring and lattice solvers.