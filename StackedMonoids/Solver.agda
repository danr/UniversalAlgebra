{-# OPTIONS --universe-polymorphism #-}

open import Data.Nat using (ℕ)
open import StackedMonoids.StackedMonoid

module StackedMonoids.Solver c ℓ (m : ℕ) (SM : StackedMonoid c ℓ m) where

open import StackedMonoids.NodeDecoratedListTree
import Algebra.FunctionProperties as FP

open import Data.Fin
open import Data.Fin.Props
open import Data.Product
open import Data.List using (List ; _∷_ ; [] ; [_] ; _++_)
open import Data.Vec using (Vec ; lookup)

open import Function using (_⟨_⟩_)

open import Relation.Nullary

open StackedMonoid SM public   
open FP _≈_

module VariableReader (v : ℕ) where

  open Operations (Fin v) (Fin m) _≟_
  
  -- Standard procedure
  
  data Expr : Set where
    var : (x : Fin v) → Expr
    ε   : (x : Fin m) → Expr
    _[_]_ : (e₁ : Expr) (∙ : Fin m) (e₂ : Expr) → Expr
  
  Env : Set c
  Env = Vec X v
  
  ⟦_⟧ : Expr → Env → X
  ⟦ var x       ⟧ Γ = lookup x Γ
  ⟦ ε n         ⟧ Γ = id n 
  ⟦ e₁ [ ∙ ] e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ ⟨ op ∙ ⟩ ⟦ e₂ ⟧ Γ
  
  Normal : Set
  Normal = NLT (Fin v) (Fin m)
  
  mutual
    ⟦_⟧″ : List Normal → Env → Fin m → X
    ⟦ []     ⟧″ Γ n = id n 
    ⟦ x ∷ xs ⟧″ Γ n = ⟦ x ⟧′ Γ ⟨ op n ⟩ ⟦ xs ⟧″ Γ n
  
    ⟦_⟧′ : Normal → Env → X
    ⟦ leaf x     ⟧′ Γ = lookup x Γ
    ⟦ branch n t ⟧′ Γ = ⟦ t ⟧″ Γ n
  
  morphism : ∀ t t′ Γ n → ⟦ t ++ t′ ⟧″ Γ n ≈ (⟦ t ⟧″ Γ n ⟨ op n ⟩ ⟦ t′ ⟧″ Γ n)
  morphism []       t′ Γ n = sym (proj₁ (identity n) (⟦ t′ ⟧″ Γ n))
  morphism (x ∷ xs) t′ Γ n = trans (cong n (refl {⟦ x ⟧′ Γ}) (morphism xs t′ Γ n))
                                   (sym (assoc n (⟦ x ⟧′ Γ) (⟦ xs ⟧″ Γ n) (⟦ t′ ⟧″ Γ n)))
  
  normalise : Expr → Normal
  normalise (var x)       = leaf x
  normalise (ε x)         = branch x []
  normalise (e₁ [ ∙ ] e₂) = (normalise e₁) ++ (normalise e₂) ⟨ ∙ ⟩
  
  homomorphic : (∙ : Fin m) (nf₁ nf₂ : Normal) (Γ : Env) 
              → ⟦ nf₁ ++ nf₂ ⟨ ∙ ⟩ ⟧′ Γ ≈ (⟦ nf₁ ⟧′ Γ ⟨ op ∙ ⟩ ⟦ nf₂ ⟧′ Γ)
  homomorphic ∙ (leaf x) (leaf x′) Γ = cong ∙ refl (proj₂ (identity ∙) (lookup x′ Γ))
  homomorphic ∙ (leaf x) (branch n t) Γ with ∙ ≟ n
  ... | yes p rewrite p = refl 
  ... | no ¬p           = cong ∙ refl (proj₂ (identity ∙) _)
  
  homomorphic ∙ (branch n t) (leaf x) Γ with ∙ ≟ n
  ... | yes p rewrite p = trans (morphism t ([ leaf x ]) Γ n) 
                                (cong n (refl {⟦ t ⟧″ Γ n}) (proj₂ (identity n) (lookup x Γ)))
  ... | no ¬p           = cong ∙ refl (proj₂ (identity ∙) (lookup x Γ))
  
  homomorphic ∙ (branch n t) (branch n′ t′) Γ with ∙ ≟ n | ∙ ≟ n′
  ... | yes p | yes p′ rewrite p | p′ = morphism t t′ Γ n′        
  ... | yes p | no ¬p′ rewrite p      = trans (morphism t ([ branch n′ t′ ]) Γ n)
                                              (cong n refl (proj₂ (identity n) (⟦ t′ ⟧″ Γ n′)))  
  ... | no ¬p | yes p′ rewrite p′     = refl
  ... | no ¬p | no ¬p′                = cong ∙ refl (proj₂ (identity ∙) _) 
  
  correct : (e : Expr) (Γ : Env) → ⟦ normalise e ⟧′ Γ ≈ ⟦ e ⟧ Γ
  correct (var x)       Γ = refl
  correct (ε x)         Γ = refl
  correct (e₁ [ ∙ ] e₂) Γ = trans (homomorphic ∙ (normalise e₁) (normalise e₂) Γ) 
                                  (cong ∙ (correct e₁ Γ) (correct e₂ Γ))
