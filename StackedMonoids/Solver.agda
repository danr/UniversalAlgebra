{-# OPTIONS --universe-polymorphism #-}

open import Data.Nat using (ℕ)
open import StackedMonoids.StackedMonoid

-- m is the number of stacked monads on top of each other
module StackedMonoids.Solver {c} {ℓ} {m : ℕ} (SM : StackedMonoid c ℓ m) where

open import StackedMonoids.NodeDecoratedListTree
import Algebra.FunctionProperties as FP

open import Data.Fin
open import Data.Fin.Props
open import Data.Product
open import Data.List using (List ; _∷_ ; [] ; [_] ; _++_)
open import Data.Vec using (Vec ; lookup)

open import Function using (_⟨_⟩_)

open import Relation.Nullary

open StackedMonoid SM 

-- The number of free variables are the same on all of these functions
module VariableReader {v : ℕ} where

  -- This gives us the union _∪_⟨_⟩ of node decorated list trees
  open Operations (Fin v) (Fin m) _≟_
  
  -- The expressions
  data Expr : Set where
    var : (x : Fin v) → Expr
    ε   : (x : Fin m) → Expr
    _[_]_ : (e₁ : Expr) (∙ : Fin m) (e₂ : Expr) → Expr
  
  -- Mapping the variables to actual values in the stacked monoid
  Env : Set c
  Env = Vec X v
  
  -- Translating an expression given an environment to a value
  ⟦_⟧ : Expr → Env → X
  ⟦ var x       ⟧ Γ = lookup x Γ
  ⟦ ε n         ⟧ Γ = id n 
  ⟦ e₁ [ ∙ ] e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ ⟨ op ∙ ⟩ ⟦ e₂ ⟧ Γ
  
  -- The node decorated list trees are the normal forms
  -- Nodes are decorated with which operator is used (m),
  -- and the values on the leaves are the variables
  Normal : Set
  Normal = NLT (Fin v) (Fin m)
  
  -- Evaluating a normal form to a value.
  mutual
    -- A little cleaner to write without a fold. 
    -- The n here is the operator to use in between.
    ⟦_⟧″ : List Normal → Env → Fin m → X
    ⟦ []     ⟧″ Γ n = id n                             -- Each operator has an identity
    ⟦ x ∷ xs ⟧″ Γ n = ⟦ x ⟧′ Γ ⟨ op n ⟩ ⟦ xs ⟧″ Γ n
  
    ⟦_⟧′ : Normal → Env → X
    ⟦ leaf x     ⟧′ Γ = lookup x Γ
    ⟦ branch n t ⟧′ Γ = ⟦ t ⟧″ Γ n

  -- Translating an expression to a normal form
  -- Notice the uses of node decorated list tree union under the operator.
  normalise : Expr → Normal
  normalise (var x)       = leaf x
  normalise (ε x)         = branch x []
  normalise (e₁ [ ∙ ] e₂) = (normalise e₁) ∪ (normalise e₂) ⟨ ∙ ⟩
  
  -- If we have two lists of normal forms, it is the same to evaluate them concatenated,
  -- or to evaluate them piece by piece and do the operator in between.
  morphism : ∀ ∙ ns₁ ns₂ Γ 
           → ⟦ ns₁ ++ ns₂ ⟧″ Γ ∙ ≈ (⟦ ns₁ ⟧″ Γ ∙ ⟨ op ∙ ⟩ ⟦ ns₂ ⟧″ Γ ∙)
  morphism ∙ []        ns₂ Γ = sym (proj₁ (identity ∙) (⟦ ns₂ ⟧″ Γ ∙))
  morphism ∙ (x ∷ ns₁) ns₂ Γ = trans (cong ∙ (refl {⟦ x ⟧′ Γ}) (morphism ∙ ns₁ ns₂ Γ))
                                     (sym (assoc ∙ (⟦ x ⟧′ Γ) (⟦ ns₁ ⟧″ Γ ∙) (⟦ ns₂ ⟧″ Γ ∙)))
  
  -- We can also use the tree merge of two normal forms under an operator
  -- this wil be the same as evaluating them and then do the operator
  homomorphic : ∀ ∙ nf₁ nf₂ Γ 
              → ⟦ nf₁ ∪ nf₂ ⟨ ∙ ⟩ ⟧′ Γ ≈ (⟦ nf₁ ⟧′ Γ ⟨ op ∙ ⟩ ⟦ nf₂ ⟧′ Γ)
  homomorphic ∙ (leaf x) (leaf x′) Γ = cong ∙ refl (proj₂ (identity ∙) (lookup x′ Γ))
  homomorphic ∙ (leaf x) (branch n t) Γ with ∙ ≟ n
  ... | yes p rewrite p = refl 
  ... | no ¬p           = cong ∙ refl (proj₂ (identity ∙) _)
  
  homomorphic ∙ (branch n t) (leaf x) Γ with ∙ ≟ n
  ... | yes p rewrite p = trans (morphism n t ([ leaf x ]) Γ) 
                                (cong n (refl {⟦ t ⟧″ Γ n}) (proj₂ (identity n) (lookup x Γ)))
  ... | no ¬p           = cong ∙ refl (proj₂ (identity ∙) (lookup x Γ))
  
  homomorphic ∙ (branch n t) (branch n′ t′) Γ with ∙ ≟ n | ∙ ≟ n′
  ... | yes p | yes p′ rewrite p | p′ = morphism n′ t t′ Γ
  ... | yes p | no ¬p′ rewrite p      = trans (morphism n t ([ branch n′ t′ ]) Γ)
                                              (cong n refl (proj₂ (identity n) (⟦ t′ ⟧″ Γ n′)))  
  ... | no ¬p | yes p′ rewrite p′     = refl
  ... | no ¬p | no ¬p′                = cong ∙ refl (proj₂ (identity ∙) _) 
  
  -- Normalising an expression and evaluating it has the same semantics
  -- as evaluating the expression
  correct : (e : Expr) (Γ : Env) → ⟦ normalise e ⟧′ Γ ≈ ⟦ e ⟧ Γ
  correct (var x)       Γ = refl
  correct (ε x)         Γ = refl
  correct (e₁ [ ∙ ] e₂) Γ = trans (homomorphic ∙ (normalise e₁) (normalise e₂) Γ) 
                                  (cong ∙ (correct e₁ Γ) (correct e₂ Γ))

open VariableReader public

-- Now we can use the reflection primitives

import Relation.Binary.Reflection as Reflection
open import Relation.Binary

open Reflection universe var ⟦_⟧ (λ e Γ → ⟦ normalise e ⟧′ Γ) correct 
  public renaming (_⊜_ to _:=_)

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