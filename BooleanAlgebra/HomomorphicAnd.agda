{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.HomomorphicAnd {β₁ β₂} (BA : BooleanAlgebra β₁ β₂) where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_] ; _>>=_ ; _++_ ; foldr) renaming (map to V-map)
open import Data.List hiding (replicate) renaming (monad to []-monad)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Maybe

open import Function

open import Category.Monad
open RawMonad []-monad

open import Relation.Binary.PropositionalEquality 
  renaming (trans to ≡-trans ; refl to ≡-refl ; sym to ≡-sym)

open import BooleanAlgebra.Member
open import BooleanAlgebra.VarSets
open import BooleanAlgebra.DNF

open BooleanAlgebra BA renaming (Carrier to X)
import BooleanAlgebra.Eval as Eval; open Eval BA

import BooleanAlgebra.Lemmas as Lemmas; open Lemmas BA

++-homomorphic : ∀ {n} (Γ : Env n) (m₁ m₂ : Meets n) → ⟦ m₁ ⟧′ Γ ∨ ⟦ m₂ ⟧′ Γ ≈ ⟦ m₁ ++ m₂ ⟧′ Γ
++-homomorphic Γ []       ms′ = proj₁ C.∨-identity (⟦ ms′ ⟧′ Γ)
++-homomorphic Γ (m ∷ ms) ms′ = ∨-assoc (⟦ m ⟧″ Γ) (⟦ ms ⟧′ Γ) (⟦ ms′ ⟧′ Γ) 
                   ⟨ trans ⟩ ∨-cong (refl {⟦ m ⟧″ Γ}) (++-homomorphic Γ ms ms′)

private
  ∩-nothing-homomorphic : ∀ {n} (Γ : Env n) (vs vs′ : VS n) 
       → (∃ λ i → lookup i vs ⋀ lookup i vs′ ≡ nothing) 
       → ⊥ ≈ ⟦ vs ⟧″ Γ ∧ ⟦ vs′ ⟧″ Γ
  ∩-nothing-homomorphic [] [] [] (() , eq)
  ∩-nothing-homomorphic (γ ∷ Γ) (v ∷ vs) (v′ ∷ vs′) (suc i , eq) = lemma₂ (∩-nothing-homomorphic Γ vs vs′ (i , eq))
  ∩-nothing-homomorphic (γ ∷ Γ) (v ∷ vs) (v′ ∷ vs′) (zero  , eq) with ⋀-nothing v v′ eq
  ... | inj₁ (eq₁ , eq₂) rewrite eq₁ | eq₂ = lemma₃ (sym (proj₂ ∧-complement γ))
  ... | inj₂ (eq₁ , eq₂) rewrite eq₁ | eq₂ = lemma₃ (sym (proj₁ ∧-complement γ))
  
  ⋀-homomorphic : (γ : X) (v v′ x : Member)
             → v ⋀ v′ ≡ just x
             → ⟦ x ⟧v γ ≈ ⟦ v ⟧v γ ∧ ⟦ v′ ⟧v γ
  ⋀-homomorphic γ T T .T ≡-refl = sym (∧-idempotent γ)
  ⋀-homomorphic γ T N _ ()
  ⋀-homomorphic γ T F .T ≡-refl = sym (proj₂ C.∧-identity γ)
  ⋀-homomorphic γ N T _ () 
  ⋀-homomorphic γ N N .N ≡-refl = sym (∧-idempotent (¬ γ))
  ⋀-homomorphic γ N F .N ≡-refl = sym (proj₂ C.∧-identity (¬ γ))
  ⋀-homomorphic γ F T .T ≡-refl = sym (proj₁ C.∧-identity γ)
  ⋀-homomorphic γ F N .N ≡-refl = sym (proj₁ C.∧-identity (¬ γ))
  ⋀-homomorphic γ F F .F ≡-refl = sym (∧-idempotent ⊤)
  
  drop-just′ : ∀ {i} {A : Set i} {x y : A} → _≡_ {i} {Maybe A} (just x) (just y) → x ≡ y
  drop-just′ ≡-refl = ≡-refl
  
  mutual
    ∩-just-cons : ∀ {n} (Γ : Env (suc n)) (v v′ : Member) (vs vs′ : VS n) x xs
           → v ⋀ v′ ≡ just x → vs ∩ vs′ ≡ just xs 
           → ⟦ x ∷ xs ⟧″ Γ ≈ ⟦ v ∷ vs ⟧″ Γ ∧ ⟦ v′ ∷ vs′ ⟧″ Γ
    ∩-just-cons (γ ∷ Γ) v v′ vs vs′ x xs eq eq′ = ⋀-homomorphic γ v v′ x eq ⟨ ∧-cong ⟩ ∩-just-homomorphic Γ vs vs′ xs eq′ 
                                            ⟨ trans ⟩ lemma₁
    
    ∩-just-homomorphic : ∀ {n} (Γ : Env n) (vs vs′ : VS n) xs
         → (vs ∩ vs′ ≡ just xs)
         → ⟦ xs ⟧″ Γ ≈ ⟦ vs ⟧″ Γ ∧ ⟦ vs′ ⟧″ Γ
    ∩-just-homomorphic [] [] [] [] ≡-refl = sym (∧-idempotent ⊤)
    ∩-just-homomorphic Γ (v ∷ vs) (v′ ∷ vs′) _ eq with ∩-just v v′ vs vs′ eq
    ∩-just-homomorphic Γ (v ∷ vs) (v′ ∷ vs′) (x ∷ xs) eq | x′ , xs′ , eq′ , eq″ rewrite eq′ | eq″ = 
                   subst (λ ─ → ⟦ ─ ⟧″ Γ ≈ ⟦ x′ ∷ xs′ ⟧″ Γ) (drop-just′ eq) refl 
         ⟨ trans ⟩ ∩-just-cons Γ v v′ vs vs′ x′ xs′ eq′ eq″
  
  ∩-homomorphic : ∀ {n} (Γ : Env n) (vs vs′ : VS n) → ⟦ maybeToList (vs ∩ vs′) ⟧′ Γ ≈ ⟦ vs ⟧″ Γ ∧ ⟦ vs′ ⟧″ Γ
  ∩-homomorphic Γ vs vs′ with inspect (vs ∩ vs′)
  ... | just xs with-≡ eq rewrite eq = proj₂ C.∨-identity (⟦ xs ⟧″ Γ) ⟨ trans ⟩ ∩-just-homomorphic Γ vs vs′ xs eq
  ... | nothing with-≡ eq rewrite eq = ∩-nothing-homomorphic Γ vs vs′ (∩-nothing vs vs′ eq)
  
  and′-homomorphic : ∀ {n} (Γ : Env n) (m : VS n) (ms : Meets n) 
                → ⟦ m ⟧″ Γ ∧ ⟦ ms ⟧′ Γ
                ≈ ⟦ (ms >>= λ t → maybeToList (m ∩ t)) ⟧′ Γ
  and′-homomorphic Γ m []        = proj₂ C.zero (⟦ m ⟧″ Γ)
  and′-homomorphic Γ m (m′ ∷ ms) = proj₁ ∧-∨-distrib (⟦ m ⟧″ Γ) (⟦ m′ ⟧″ Γ) (⟦ ms ⟧′ Γ)  
                              ⟨ trans ⟩ (sym (∩-homomorphic Γ m m′) ⟨ ∨-cong ⟩ and′-homomorphic Γ m ms)
                              ⟨ trans ⟩ ++-homomorphic Γ (maybeToList (m ∩ m′)) 
                                                      (ms >>= λ t → maybeToList (m ∩ t)) 
  
and-homomorphic : ∀ {n} (Γ : Env n) (m₁ m₂ : Meets n)
             → ⟦ m₁ ⟧′ Γ ∧ ⟦ m₂ ⟧′ Γ 
             ≈ ⟦ (m₁ >>= λ t₁ → m₂  >>= λ t₂ → maybeToList (t₁ ∩ t₂)) ⟧′ Γ
and-homomorphic Γ []       m₂ = proj₁ C.zero (⟦ m₂ ⟧′ Γ)
and-homomorphic Γ (m ∷ ms) m₂ = proj₂ ∧-∨-distrib (⟦ m₂ ⟧′ Γ) (⟦ m ⟧″ Γ) (⟦ ms ⟧′ Γ) 
                           ⟨ trans ⟩ (and′-homomorphic Γ m m₂ ⟨ ∨-cong ⟩ and-homomorphic Γ ms m₂) 
                           ⟨ trans ⟩ ++-homomorphic Γ (m₂ >>= λ t → maybeToList (m ∩ t)) 
                                                   (ms >>= λ t₁ → m₂ >>= λ t₂ → maybeToList (t₁ ∩ t₂))

