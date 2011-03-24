{-# OPTIONS --universe-polymorphism #-}
module BooleanAlgebra.VarSets where

open import Data.Nat hiding (_<_ ; compare)
open import Data.Vec hiding (drop ; _∈_ ; map ; [_])
open import Data.Fin hiding (_<_ ; compare)
open import Data.List hiding (replicate ; drop)
open import Data.Product hiding (map)
open import Data.Maybe
open import Data.Sum
open import Data.Empty

open import Function

open import BooleanAlgebra.Member

open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.List.StrictLex as Lex

MemberListLexOrder : StrictTotalOrder _ _ _
MemberListLexOrder = <-strictTotalOrder Member-Order 

open StrictTotalOrder MemberListLexOrder public using (compare) 

VS : ℕ → Set
VS = Vec Member

singleton : ∀ {n} → Fin n → VS n
singleton zero    = T ∷ replicate F
singleton (suc n) = F ∷ singleton n

_∩_ : ∀ {n} → VS n → VS n → Maybe (VS n)
[]       ∩ []       = just []
(x ∷ xs) ∩ (y ∷ ys) with x ⋀ y | xs ∩ ys
... | just v | just vs = just (v ∷ vs)
... | _      | _       = nothing

private
  ∩-lemma : ∀ {n} v v′ → (vs vs′ : VS n) → (v ∷ vs) ∩ (v′ ∷ vs′) ≡ nothing → vs ∩ vs′ ≡ nothing ⊎ v ⋀ v′ ≡ nothing
  ∩-lemma v v′ vs vs′ eq with v ⋀ v′ | vs ∩ vs′
  ∩-lemma v v′ vs vs′ () | just v″ | just vs″
  ... | nothing | just vs″ = inj₂ refl
  ... | _       | nothing  = inj₁ refl

  just∧nothing→⁇ : ∀ {A : Set} {x : Maybe A} {v : A} → x ≡ nothing → x ≡ just v → ∀ {⁇ : Set} → ⁇
  just∧nothing→⁇ {x = just _}   () eq
  just∧nothing→⁇ {x = nothing}  eq ()

∩-nothing : ∀ {n} → (vs vs′ : VS n) → vs ∩ vs′ ≡ nothing → ∃ λ i → lookup i vs ⋀ lookup i vs′ ≡ nothing
∩-nothing [] [] ()
∩-nothing (x ∷ xs) (y ∷ ys) eq with inspect (x ⋀ y)
... | nothing with-≡ eq′ = zero , eq′
... | just v  with-≡ eq′ with ∩-lemma x y xs ys eq
... | inj₂ eq″ = just∧nothing→⁇ eq″ eq′
... | inj₁ eq″ with ∩-nothing xs ys eq″
... | i , eq‴ = suc i , eq‴

⋀-nothing : ∀ x y → x ⋀ y ≡ nothing → (x ≡ T × y ≡ N) ⊎ (x ≡ N × y ≡ T)
⋀-nothing T N = λ x' → inj₁ (refl , refl)
⋀-nothing N T = λ x' → inj₂ (refl , refl)
⋀-nothing T T = λ ()
⋀-nothing T F = λ ()
⋀-nothing N N = λ ()
⋀-nothing N F = λ ()
⋀-nothing F _ = λ ()
  
∩-just : ∀ {n} (v v′ : Member) {xs : VS (suc n)} (vs vs′ : VS n) 
       → ((v ∷ vs) ∩ (v′ ∷ vs′)) ≡ (just xs)
       → ∃₂ λ v″ vs″ → v ⋀ v′ ≡ just v″ × vs ∩ vs′ ≡ just vs″
∩-just v v′ vs vs′ eq with v ⋀ v′ | vs ∩ vs′
∩-just v v′ vs vs′ eq | just v″ | just vs″  = v″ , vs″ , refl , refl
∩-just v v′ vs vs′ () | nothing | just _  
∩-just v v′ vs vs′ () | nothing | nothing 
∩-just v v′ vs vs′ () | just _  | nothing 

maybeToList : ∀ {i} {A : Set i} → Maybe A → List A
maybeToList (just x) = [ x ]
maybeToList nothing  = []

Meets : ℕ → Set
Meets n = List (VS n)

data _⊆_ : ∀ {n} → VS n → VS n → Set where
  stop   : [] ⊆ []
  keep-T : ∀   {n} {xs ys : VS n} → xs ⊆ ys → (T ∷ xs) ⊆ (T ∷ ys)
  keep-N : ∀   {n} {xs ys : VS n} → xs ⊆ ys → (N ∷ xs) ⊆ (N ∷ ys)
  drop   : ∀ x {n} {xs ys : VS n} → xs ⊆ ys → (F ∷ xs) ⊆ (x ∷ ys)

_⊈_ : ∀ {n} → VS n → VS n → Set
A ⊈ B = A ⊆ B → ⊥

tail-⊆ : ∀ {n x y} {xs ys : VS n} → (x ∷ xs) ⊆ (y ∷ ys) → xs ⊆ ys
tail-⊆ (keep-T y) = y
tail-⊆ (keep-N y) = y
tail-⊆ (drop _ y) = y

_⊆?_ : ∀ {n} → Decidable (_⊆_ {n})
[]       ⊆? [] = yes stop
(x ∷ xs) ⊆? (y ∷ ys) with xs ⊆? ys
(T ∷ xs) ⊆? (T ∷ ys) | yes p = yes (keep-T p)
(N ∷ xs) ⊆? (N ∷ ys) | yes p = yes (keep-N p)
(F ∷ xs) ⊆? (y ∷ ys) | yes p = yes (drop y p) 
(T ∷ xs) ⊆? (F ∷ ys) | yes p = no λ()
(N ∷ xs) ⊆? (F ∷ ys) | yes p = no λ()
(T ∷ xs) ⊆? (N ∷ ys) | yes p = no λ()
(N ∷ xs) ⊆? (T ∷ ys) | yes p = no λ()
(x ∷ xs) ⊆? (y ∷ ys) | no ¬p = no (¬p ∘ tail-⊆)
