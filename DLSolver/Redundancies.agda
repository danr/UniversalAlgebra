{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module DLSolver.Redundancies {δ₁ δ₂} (DL : DistributiveLattice δ₁ δ₂) where

open import Data.Vec using (_∷_ ; [])
open import Data.List.NonEmpty hiding (tail ; head ; SnocView ; last)
open import Data.List.Any as Any hiding (tail ; map)
open Any.Membership-≡ hiding (_⊆_ ; _⊈_)
open import Data.ParallelList
open import Data.Product 
open import Data.Empty 

open import Function

open import Relation.Binary
open import Relation.Nullary hiding (¬_)

open import Relation.Binary.PropositionalEquality hiding (trans ; sym) renaming (refl to ≡-refl)

open import DLSolver.VarSets
open import DLSolver.DNF

open DistributiveLattice DL renaming (Carrier to X)
import DLSolver.Eval as Eval; open Eval DL
import DLSolver.Lemmas as Lemmas; open Lemmas DL

------------------------------------------------------------------------
-- Say we have a DNF formula m₁ ∧ m₂ ∧ … ∧ mn.
-- Then m′ is redundant if ∃ λ i → mi ⊆ m′
-- Converesly, We say m′ is necessary if ∀ i → mi ⊈ m
--
-- Say m ⊆ m′, then m′ is redundant because for some ai and bi we have:
-- m  = a₁ ∧ … ∧ an
-- m′ = a₁ ∧ … ∧ an ∧ b₁ ∧ … ∧ bn′  (since it is a superset of the vars)
-- Let's denote m′ = m ∧ b
-- Then m v m′ ≈ m ∨ (m ∧ b) ≈ m, by absorption, so m′ is indeed redundant.

Necessary : ∀ {n} → VS n → DNF n → Set
Necessary m′ ms = ParList (λ m → m ⊈ m′) (toList ms)

Redundant : ∀ {n} → VS n → DNF n → Set
Redundant m′ ms = ∃ λ m → m ∈ toList ms × m ⊆ m′

------------------------------------------------------------------------
-- We can constructively show that we cannot both have necessity and 
-- redundancy at the same time.

¬Necessary→Redundant : ∀ {n} (m′ : VS n) (ms : DNF n) → (Necessary m′ ms → ⊥) → Redundant m′ ms
¬Necessary→Redundant m′ [ m ]    ¬Nec with m ⊆? m′
... | yes p = m , here ≡-refl , p
... | no ¬p = ⊥-elim (¬Nec (¬p ∷ []))
¬Necessary→Redundant m′ (m ∷ ms) ¬Nec with m ⊆? m′
... | yes p = m , here ≡-refl , p
... | no ¬p with ¬Necessary→Redundant m′ ms (λ ¬ps → ¬Nec (¬p ∷ ¬ps))
... | m' , m'∈ms , m'⊆m′ = m' , there m'∈ms , m'⊆m′

¬Redundant→Necessary : ∀ {n} (m′ : VS n) (ms : DNF n) → (Redundant m′ ms → ⊥) → Necessary m′ ms
¬Redundant→Necessary m′ [ m ]    ¬Red = (λ m⊆m′ → ¬Red (m , here ≡-refl , m⊆m′)) ∷ []
¬Redundant→Necessary m′ (m ∷ ms) ¬Red = (λ m⊆m′ → ¬Red (m , here ≡-refl , m⊆m′)) 
                                      ∷ ¬Redundant→Necessary m′ ms 
                                              (λ xs → ¬Red ( proj₁ xs
                                                           , there (proj₁ (proj₂ xs)) 
                                                           , proj₂ (proj₂ xs)))

Redundant∧Necessary→⊥ : ∀ {n} (m′ : VS n) (ms : DNF n) → Redundant m′ ms → Necessary m′ ms → ⊥
Redundant∧Necessary→⊥ m′ [ m ]     (_  , there () , _)  _ 
Redundant∧Necessary→⊥ m′ [ m ]     (.m , here ≡-refl , m⊆m′)  (p ∷ []) = p m⊆m′
Redundant∧Necessary→⊥ m′ (m  ∷ ms) (.m , here ≡-refl , m⊆m′)  (p ∷ ps) = p m⊆m′
Redundant∧Necessary→⊥ m′ (m″ ∷ ms) (m  , there pxs   , m⊆m′) (p ∷ ps) 
                                         = Redundant∧Necessary→⊥ m′ ms (m , pxs , m⊆m′) ps

------------------------------------------------------------------------
-- Necessity/redundancy is decidable

necessary? : ∀ {n} → Decidable (Necessary {n})
necessary? m′ [ m ]    with m ⊆? m′
... | yes p = no (Redundant∧Necessary→⊥ m′ [ m ] (m , here ≡-refl , p))
... | no p  = yes (p ∷ [])
necessary? m′ (m ∷ ms) with m ⊆? m′
... | yes p = no (Redundant∧Necessary→⊥ m′ (m ∷ ms) (m , here ≡-refl , p))
... | no ¬p with necessary? m′ ms
... | yes p′ = yes (¬p ∷ p′)
... | no ¬p′ = no (¬p′ ∘ tail)

------------------------------------------------------------------------
-- Given a necessary m′ and m₁ ∨ ... ∨ mn
-- insert m′ and remove all mi st m′ ⊆ m

removeDependencies : ∀ {n} → VS n → DNF n → DNF n
removeDependencies m′ [ m ]    with m′ ⊆? m
... | yes p = [ m′ ] 
... | no ¬p = m′ ∷ [ m ]
removeDependencies m′ (m ∷ ms) with m′ ⊆? m
... | yes p = removeDependencies m′ ms
... | no ¬p = m ∷ removeDependencies m′ ms

------------------------------------------------------------------------
-- Given a formula in DNF, decide which are necessary
-- and remove all their dependencies

removeRedundancies : ∀ {n} → DNF n → DNF n
removeRedundancies [ m ] = [ m ]
removeRedundancies (m ∷ ms) with necessary? m ms
... | yes p = removeDependencies m (removeRedundancies ms)
... | no ¬p = removeRedundancies ms

------------------------------------------------------------------------
-- If we have that m′ is necessary in a DNF formula
-- then it is still necessary if we remove its dependencies.

Necessary-rmDep : ∀ {n} (m m′ : VS n) → m ⊈ m′ → (ms : DNF n) 
                → Necessary m′ ms → Necessary m′ (removeDependencies m ms)
Necessary-rmDep m′ m m⊈m′ [ m″ ]    (n ∷ []) with m′ ⊆? m″
... | yes p = m⊈m′ ∷ [] 
... | no ¬p = m⊈m′ ∷ (n ∷ [])
Necessary-rmDep m′ m m⊈m′ (m″ ∷ ms) (n ∷ ns) with m′ ⊆? m″
... | yes p = Necessary-rmDep m′ m m⊈m′ ms ns
... | no ¬p = n ∷ (Necessary-rmDep m′ m m⊈m′ ms ns)

------------------------------------------------------------------------
-- Similarly, if m′ is necessary we can remove all redunancies
-- (and their dependencies), and m′ is still necessary

Necessary-rmReds : ∀ {n} (m′ : VS n) (ms : DNF n) 
                     → Necessary m′ ms → Necessary m′ (removeRedundancies ms)
Necessary-rmReds m′ [ m ]    (p ∷ []) = p ∷ []
Necessary-rmReds m′ (m ∷ ms) (n ∷ ns) with necessary? m ms
... | yes p = Necessary-rmDep m m′ n (removeRedundancies ms) (Necessary-rmReds m′ ms ns)
... | no ¬p = Necessary-rmReds m′ ms ns

------------------------------------------------------------------------
-- If m ⊆ m′, then we can remove it without changing the evaluated value.
-- Here we use absorption (lemma₅ uses absorption, too).

rm-⊆-correct : ∀ {n} (Γ : Env n) {m m′ : VS n}
              → m ⊆ m′ 
              → ⟦ m ⟧″ Γ ∨ ⟦ m′ ⟧″ Γ ≈ ⟦ m ⟧″ Γ
rm-⊆-correct Γ last = ∨-idempotent _
rm-⊆-correct (γ ∷ Γ) (stop vs′)      = proj₁ absorptive γ _
rm-⊆-correct (γ ∷ Γ) (keep vs⊆vs′)   = lemma₄ (rm-⊆-correct Γ vs⊆vs′)
rm-⊆-correct (γ ∷ Γ) (drop-T vs⊆vs′) = lemma₅ (rm-⊆-correct Γ vs⊆vs′) 
rm-⊆-correct (γ ∷ Γ) (drop-F vs⊆vs′) = rm-⊆-correct Γ vs⊆vs′

------------------------------------------------------------------------
-- If a conjunct is necessary, we can safely remove all its dependencies 

rmDep-correct : ∀ {n} (Γ : Env n) (m′ : VS n) (ms : DNF n)
              → Necessary m′ ms
              → ⟦ m′ ⟧″ Γ ∨ ⟦ ms ⟧′ Γ ≈ ⟦ removeDependencies m′ ms ⟧′ Γ
rmDep-correct Γ m′ [ m ]    (n ∷ []) with m′ ⊆? m
... | yes p = rm-⊆-correct Γ p 
... | no ¬p = refl
rmDep-correct Γ m′ (m ∷ ms) (n ∷ ns) with m′ ⊆? m
... | yes p = sym (∨-assoc _ _ _) 
            ⟨ trans ⟩ (rm-⊆-correct Γ p ⟨ ∨-cong ⟩ refl) 
            ⟨ trans ⟩ rmDep-correct Γ m′ ms ns
... | no ¬p = lemma₆ ⟨ trans ⟩ (refl ⟨ ∨-cong ⟩ rmDep-correct Γ m′ ms ns) 

-- If a conjunct is redundant, we can safely remove it.
rmRed-correct : ∀ {n} (Γ : Env n) (m′ : VS n) (ms : DNF n)
            → Redundant m′ ms
            → ⟦ m′ ⟧″ Γ ∨ ⟦ ms ⟧′ Γ ≈ ⟦ ms ⟧′ Γ
rmRed-correct Γ m′ [ m ] (.m , here ≡-refl , m⊆m′) 
  = ∨-comm _ _ ⟨ trans ⟩ rm-⊆-correct Γ m⊆m′
rmRed-correct Γ m′ [ m ] (m″ , there ()    , m⊆m′)
rmRed-correct Γ m′ (m ∷ ms) (.m , here ≡-refl , m⊆m′) 
  = lemma₆ ⟨ trans ⟩ sym (∨-assoc _ _ _) ⟨ trans ⟩ 
    (rm-⊆-correct Γ m⊆m′ ⟨ ∨-cong ⟩ refl)
rmRed-correct Γ m′ (m″ ∷ ms) (m , there m∈ms , m⊆m′) 
  = lemma₆ ⟨ trans ⟩ (refl ⟨ ∨-cong ⟩ rmRed-correct Γ m′ ms (m , m∈ms , m⊆m′))
  
------------------------------------------------------------------------
-- Removing all redundancies from a DNF formula does not change the value

rmReds-correct : ∀ {n} (Γ : Env n) (ms : DNF n)
               → ⟦ ms ⟧′ Γ ≈ ⟦ removeRedundancies ms ⟧′ Γ
rmReds-correct Γ [ m ]    = refl
rmReds-correct Γ (m ∷ ms) with necessary? m ms
... | yes p = refl ⟨ ∨-cong ⟩ rmReds-correct Γ ms 
            ⟨ trans ⟩ rmDep-correct Γ m (removeRedundancies ms) 
                                        (Necessary-rmReds m ms p)
... | no ¬p = rmRed-correct Γ m ms (¬Necessary→Redundant m ms ¬p) 
            ⟨ trans ⟩ rmReds-correct Γ ms
  
       