{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.Solver {β₁ β₂} (BA : BooleanAlgebra β₁ β₂) where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_] ; _>>=_ ; _++_ ; foldr) renaming (map to V-map)
open import Data.List hiding (replicate) renaming (monad to []-monad)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Maybe
open import BooleanAlgebra.Member
open import BooleanAlgebra.VarSets
open import Category.Monad
open import Function

open import Relation.Binary.PropositionalEquality renaming (trans to ≡-trans ; refl to ≡-refl ; sym to ≡-sym)

open BooleanAlgebra BA renaming (Carrier to X)
import Algebra.Props.BooleanAlgebra as P-BA; open P-BA BA
import BooleanAlgebra.Lemmas as Lemmas; open Lemmas BA

module C = CommutativeSemiring ∨-∧-commutativeSemiring 
  renaming (+-identity to ∨-identity ; *-identity to ∧-identity) 

open RawMonad []-monad
  
data Expr (n : ℕ) : Set where
  var        : (x : Fin n) → Expr n
  top bottom : Expr n
  neg        : (e : Expr n) → Expr n
  _and_ _or_ : (e₁ e₂ : Expr n) → Expr n

DNF : ∀ {n} → Expr n → Meets n
DNF (var x)     = [ singleton x ]
DNF top         = [ replicate F ]
DNF bottom      = []
DNF (neg e)     = map (V-map not) (DNF e)
DNF (e₁ or  e₂) = DNF e₁ ++ DNF e₂  
DNF (e₁ and e₂) = DNF e₁ >>= λ t₁ → DNF e₂ >>= λ t₂ → maybeToList (t₁ ∩ t₂)

-- DNF is not the "most normal" form, we need to remove redundancies. 
-- Use _⋃_ from VarSets
-- I am not sure to do this inside the DNF or afterwards.
-- Need to preserve the swaps or the bag equality to use to know when the commutativity is

Env : ℕ → Set β₁
Env n = Vec X n

⟦_⟧ : ∀ {n} → Expr n → Env n → X
⟦ var x     ⟧ Γ = lookup x Γ
⟦ top       ⟧ Γ = ⊤
⟦ bottom    ⟧ Γ = ⊥
⟦ neg e     ⟧ Γ = ⟦ e ⟧ (V-map ¬_ Γ)
⟦ e₁ and e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ ∧ ⟦ e₂ ⟧ Γ
⟦ e₁ or e₂  ⟧ Γ = ⟦ e₁ ⟧ Γ ∨ ⟦ e₂ ⟧ Γ

⟦_⟧v : Member → X → X
⟦_⟧v T γ =   γ
⟦_⟧v N γ = ¬ γ
⟦_⟧v F γ =   ⊤

⟦_⟧″ : ∀ {n} → VS n → Env n → X
⟦ []     ⟧″ []      = ⊤
⟦ x ∷ xs ⟧″ (γ ∷ Γ) = ⟦ x ⟧v γ ∧ ⟦ xs ⟧″ Γ

⟦_⟧′ : ∀ {n} → Meets n → Env n → X
⟦ []     ⟧′ Γ = ⊥
⟦ M ∷ Ms ⟧′ Γ = ⟦ M ⟧″ Γ ∨ ⟦ Ms ⟧′ Γ

var-morphism : ∀ {n} (Γ : Env n) (x : Fin n) → ⟦ var x ⟧ Γ ≈ ⟦ DNF (var x) ⟧′ Γ
var-morphism [] ()
var-morphism (γ ∷ [])     zero    = sym (proj₂ C.∧-identity γ) ⟨ trans ⟩
                                    sym (proj₂ C.∨-identity (γ ∧ ⊤))
var-morphism (γ ∷ γ′ ∷ Γ) zero    = var-morphism (γ ∷ Γ) zero ⟨ trans ⟩ 
                                    (refl {γ} ⟨ ∧-cong ⟩ sym (proj₁ C.∧-identity _) ⟨ ∨-cong ⟩ refl {⊥}) 
var-morphism (γ ∷ Γ)      (suc x) = var-morphism Γ x ⟨ trans ⟩ 
                                    (sym (proj₁ C.∧-identity _) ⟨ ∨-cong ⟩ refl {⊥}) 

top-morphism : ∀ {n} (Γ : Env n) → ⟦ top ⟧ Γ ≈ ⟦ DNF top ⟧′ Γ
top-morphism []      = sym (proj₂ C.∨-identity ⊤)
top-morphism (γ ∷ Γ) = top-morphism Γ ⟨ trans ⟩ 
                       (sym (proj₁ C.∧-identity _) ⟨ ∨-cong ⟩ refl {⊥}) 

neg′-morphism : ∀ {n} (Γ : Env n) (vs : VS n) → ⟦ vs ⟧″ (V-map ¬_ Γ) ≈ ⟦ V-map not vs ⟧″ Γ
neg′-morphism []      []       = refl
neg′-morphism (γ ∷ Γ) (T ∷ vs) = refl {¬ γ}     ⟨ ∧-cong ⟩ neg′-morphism Γ vs
neg′-morphism (γ ∷ Γ) (N ∷ vs) = ¬-involutive γ ⟨ ∧-cong ⟩ neg′-morphism Γ vs
neg′-morphism (γ ∷ Γ) (F ∷ vs) = refl {⊤}       ⟨ ∧-cong ⟩ neg′-morphism Γ vs 

neg-morphism : ∀ {n} (Γ : Env n) (m : Meets n) → ⟦ m ⟧′ (V-map ¬_ Γ) ≈ ⟦ map (V-map not) m ⟧′ Γ
neg-morphism Γ []       = refl
neg-morphism Γ (m ∷ ms) = neg′-morphism Γ m ⟨ ∨-cong ⟩ neg-morphism Γ ms

++-morphism : ∀ {n} (Γ : Env n) (m₁ m₂ : Meets n) → ⟦ m₁ ⟧′ Γ ∨ ⟦ m₂ ⟧′ Γ ≈ ⟦ m₁ ++ m₂ ⟧′ Γ
++-morphism Γ []       ms′ = proj₁ C.∨-identity (⟦ ms′ ⟧′ Γ)
++-morphism Γ (m ∷ ms) ms′ = ∨-assoc (⟦ m ⟧″ Γ) (⟦ ms ⟧′ Γ) (⟦ ms′ ⟧′ Γ) 
                   ⟨ trans ⟩ ∨-cong (refl {⟦ m ⟧″ Γ}) (++-morphism Γ ms ms′)

∩-nm : ∀ {n} (Γ : Env n) (vs vs′ : VS n) 
     → (∃ λ i → lookup i vs ⋀ lookup i vs′ ≡ nothing) 
     → ⊥ ≈ ⟦ vs ⟧″ Γ ∧ ⟦ vs′ ⟧″ Γ
∩-nm [] [] [] (() , eq)
∩-nm (γ ∷ Γ) (v ∷ vs) (v′ ∷ vs′) (suc i , eq) = lemma₂ (∩-nm Γ vs vs′ (i , eq))
∩-nm (γ ∷ Γ) (v ∷ vs) (v′ ∷ vs′) (zero  , eq) with ⋀-nothing v v′ eq
... | inj₁ (eq₁ , eq₂) rewrite eq₁ | eq₂ = lemma₃ (sym (proj₂ ∧-complement γ))
... | inj₂ (eq₁ , eq₂) rewrite eq₁ | eq₂ = lemma₃ (sym (proj₁ ∧-complement γ))

⋀-morphism : (γ : X) (v v′ x : Member)
           → v ⋀ v′ ≡ just x
           → ⟦ x ⟧v γ ≈ ⟦ v ⟧v γ ∧ ⟦ v′ ⟧v γ
⋀-morphism γ T T .T ≡-refl = sym (∧-idempotent γ)
⋀-morphism γ T N _ ()
⋀-morphism γ T F .T ≡-refl = sym (proj₂ C.∧-identity γ)
⋀-morphism γ N T _ () 
⋀-morphism γ N N .N ≡-refl = sym (∧-idempotent (¬ γ))
⋀-morphism γ N F .N ≡-refl = sym (proj₂ C.∧-identity (¬ γ))
⋀-morphism γ F T .T ≡-refl = sym (proj₁ C.∧-identity γ)
⋀-morphism γ F N .N ≡-refl = sym (proj₁ C.∧-identity (¬ γ))
⋀-morphism γ F F .F ≡-refl = sym (∧-idempotent ⊤)

drop-just′ : ∀ {i} {A : Set i} {x y : A} → _≡_ {i} {Maybe A} (just x) (just y) → x ≡ y
drop-just′ ≡-refl = ≡-refl

mutual
  ∩-j : ∀ {n} (Γ : Env (suc n)) (v v′ : Member) (vs vs′ : VS n) x xs
         → v ⋀ v′ ≡ just x → vs ∩ vs′ ≡ just xs 
         → ⟦ x ∷ xs ⟧″ Γ ≈ ⟦ v ∷ vs ⟧″ Γ ∧ ⟦ v′ ∷ vs′ ⟧″ Γ
  ∩-j (γ ∷ Γ) v v′ vs vs′ x xs eq eq′ = ⋀-morphism γ v v′ x eq ⟨ ∧-cong ⟩ ∩-jm Γ vs vs′ xs eq′ 
                                          ⟨ trans ⟩ lemma₁
  
  ∩-jm : ∀ {n} (Γ : Env n) (vs vs′ : VS n) xs
       → (vs ∩ vs′ ≡ just xs)
       → ⟦ xs ⟧″ Γ ≈ ⟦ vs ⟧″ Γ ∧ ⟦ vs′ ⟧″ Γ
  ∩-jm [] [] [] [] ≡-refl = sym (∧-idempotent ⊤)
  ∩-jm Γ (v ∷ vs) (v′ ∷ vs′) _ eq with ∩-just v v′ vs vs′ eq
  ∩-jm Γ (v ∷ vs) (v′ ∷ vs′) (x ∷ xs) eq | x′ , xs′ , eq′ , eq″ rewrite eq′ | eq″ = 
                 subst (λ ─ → ⟦ ─ ⟧″ Γ ≈ ⟦ x′ ∷ xs′ ⟧″ Γ) (drop-just′ eq) refl 
       ⟨ trans ⟩ ∩-j Γ v v′ vs vs′ x′ xs′ eq′ eq″

∩-morphism : ∀ {n} (Γ : Env n) (vs vs′ : VS n) → ⟦ maybeToList (vs ∩ vs′) ⟧′ Γ ≈ ⟦ vs ⟧″ Γ ∧ ⟦ vs′ ⟧″ Γ
∩-morphism Γ vs vs′ with inspect (vs ∩ vs′)
... | just xs with-≡ eq rewrite eq = proj₂ C.∨-identity (⟦ xs ⟧″ Γ) ⟨ trans ⟩ ∩-jm Γ vs vs′ xs eq
... | nothing with-≡ eq rewrite eq = ∩-nm Γ vs vs′ (∩-nothing vs vs′ eq)

and′-morphism : ∀ {n} (Γ : Env n) (m : VS n) (ms : Meets n) 
              → ⟦ m ⟧″ Γ ∧ ⟦ ms ⟧′ Γ
              ≈ ⟦ (ms >>= λ t → maybeToList (m ∩ t)) ⟧′ Γ
and′-morphism Γ m []        = proj₂ C.zero (⟦ m ⟧″ Γ)
and′-morphism Γ m (m′ ∷ ms) = proj₁ ∧-∨-distrib (⟦ m ⟧″ Γ) (⟦ m′ ⟧″ Γ) (⟦ ms ⟧′ Γ)  
                            ⟨ trans ⟩ (sym (∩-morphism Γ m m′) ⟨ ∨-cong ⟩ and′-morphism Γ m ms)
                            ⟨ trans ⟩ ++-morphism Γ (maybeToList (m ∩ m′)) 
                                                    (ms >>= λ t → maybeToList (m ∩ t)) 

and-morphism : ∀ {n} (Γ : Env n) (m₁ m₂ : Meets n)
             → ⟦ m₁ ⟧′ Γ ∧ ⟦ m₂ ⟧′ Γ 
             ≈ ⟦ (m₁ >>= λ t₁ → m₂  >>= λ t₂ → maybeToList (t₁ ∩ t₂)) ⟧′ Γ
and-morphism Γ []       m₂ = proj₁ C.zero (⟦ m₂ ⟧′ Γ)
and-morphism Γ (m ∷ ms) m₂ = proj₂ ∧-∨-distrib (⟦ m₂ ⟧′ Γ) (⟦ m ⟧″ Γ) (⟦ ms ⟧′ Γ) 
                           ⟨ trans ⟩ (and′-morphism Γ m m₂ ⟨ ∨-cong ⟩ and-morphism Γ ms m₂) 
                           ⟨ trans ⟩ ++-morphism Γ (m₂ >>= λ t → maybeToList (m ∩ t)) 
                                                   (ms >>= λ t₁ → m₂ >>= λ t₂ → maybeToList (t₁ ∩ t₂))


DNF-correct : ∀ {n} (Γ : Env n) (e : Expr n) → ⟦ e ⟧ Γ ≈ ⟦ DNF e ⟧′ Γ
DNF-correct Γ (var x)     = var-morphism Γ x
DNF-correct Γ top         = top-morphism Γ
DNF-correct Γ bottom      = refl
DNF-correct Γ (neg e)     = DNF-correct (V-map ¬_ Γ) e ⟨ trans ⟩ neg-morphism Γ (DNF e)
DNF-correct Γ (e₁ and e₂) = ∧-cong (DNF-correct Γ e₁) (DNF-correct Γ e₂) 
                          ⟨ trans ⟩ and-morphism Γ (DNF e₁) (DNF e₂)
DNF-correct Γ (e₁ or e₂)  = ∨-cong (DNF-correct Γ e₁) (DNF-correct Γ e₂) 
                          ⟨ trans ⟩ ++-morphism Γ (DNF e₁) (DNF e₂)
