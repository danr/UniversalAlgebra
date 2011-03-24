{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.Redundancies {β₁ β₂} (BA : BooleanAlgebra β₁ β₂) where

open import Data.Nat 
open import Data.Fin 
open import Data.Vec hiding ([_] ; _>>=_ ; _++_ ; foldr ; tail ; _∈_ ; drop) renaming (map to V-map)
open import Data.List hiding (replicate ; drop) renaming (monad to []-monad)
open import Data.List.Any as Any hiding (tail ; map)
open Any.Membership-≡ hiding (_⊆_ ; _⊈_)
open import Data.ParallelList
open import Data.Product hiding (map)
open import Data.Empty renaming (⊥ to ∅ ; ⊥-elim to ∅-elim)

open import Function

open import Relation.Binary
open import Relation.Nullary hiding (¬_)
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary.PropositionalEquality 
  renaming (trans to ≡-trans ; refl to ≡-refl ; sym to ≡-sym)

open import BooleanAlgebra.Member
open import BooleanAlgebra.VarSets
open import BooleanAlgebra.DNF

open BooleanAlgebra BA renaming (Carrier to X)
import BooleanAlgebra.Eval as Eval; open Eval BA
import BooleanAlgebra.Lemmas as Lemmas; open Lemmas BA

-- We have meets : M₁ ∧ M₂ ∧ ... ∧ Mn
-- M′ is redundant if ∃ i . Mi ⊆ M′
-- We say M′ is necessary if ∀ i . Mi ⊈ M′

Necessary : ∀ {n} → VS n → Meets n → Set
Necessary M′ Ms = ParList (λ M → M ⊈ M′) Ms

Redundant : ∀ {n} → VS n → Meets n → Set
Redundant M′ Ms = ∃ λ M → M ∈ Ms × M ⊆ M′

-- As expected, they are inverses of each other.
¬Necessary→Redundant : ∀ {n} (M′ : VS n) (Ms : Meets n) → (Necessary M′ Ms → ∅) → Redundant M′ Ms
¬Necessary→Redundant M′ []       ¬Nec = ∅-elim (¬Nec [])
¬Necessary→Redundant M′ (M ∷ Ms) ¬Nec with M ⊆? M′
... | yes p = M , here ≡-refl , p
... | no ¬p with ¬Necessary→Redundant M′ Ms (λ ¬ps → ¬Nec (¬p ∷ ¬ps))
... | M' , M'∈Ms , M'⊆M′ = M' , there M'∈Ms , M'⊆M′

¬Redundant→Necessary : ∀ {n} (M′ : VS n) (Ms : Meets n) → (Redundant M′ Ms → ∅) → Necessary M′ Ms
¬Redundant→Necessary M′ []       ¬Red = []
¬Redundant→Necessary M′ (M ∷ Ms) ¬Red = (λ M⊆M′ → ¬Red (M , here ≡-refl , M⊆M′)) 
                                      ∷ ¬Redundant→Necessary M′ Ms 
                                              (λ xs → ¬Red ( proj₁ xs
                                                           , there (proj₁ (proj₂ xs)) 
                                                           , proj₂ (proj₂ xs)))

Redundant∧Necessary→∅ : ∀ {n} (M′ : VS n) (Ms : Meets n) → Redundant M′ Ms → Necessary M′ Ms → ∅
Redundant∧Necessary→∅ M′ []       (_ , () , _)         Nec
Redundant∧Necessary→∅ M′ (M ∷ Ms) (.M , here ≡-refl , M⊆M′)  (p ∷ ps) = p M⊆M′
Redundant∧Necessary→∅ M′ (M ∷ Ms) (M' , there pxs , M'⊆M′) (p ∷ ps) = 
  Redundant∧Necessary→∅ M′ Ms (M' , pxs , M'⊆M′) ps

-- Necessity is decidable
necessary? : ∀ {n} → Decidable (Necessary {n})
necessary? M′ []       = yes []
necessary? M′ (M ∷ Ms) with M ⊆? M′
... | yes p = no (Redundant∧Necessary→∅ M′ (M ∷ Ms) (M , here ≡-refl , p))
... | no ¬p with necessary? M′ Ms
... | yes p′ = yes (¬p ∷ p′)
... | no ¬p′ = no (¬p′ ∘ tail)

-- Given M′ and M₁ ∨ ... ∨ Mn
-- insert M′ and remove all Mi st M′ ⊆ M
-- Only run this when M′ is necessary
removeDependencies : ∀ {n} → VS n → Meets n → Meets n
removeDependencies M′ []       = [ M′ ]
removeDependencies M′ (M ∷ Ms) with M′ ⊆? M
... | yes p = removeDependencies M′ Ms
... | no ¬p = M ∷ removeDependencies M′ Ms

-- Given all the meets, decide which are necessary
-- and remove all their dependencies
removeRedundancies : ∀ {n} → Meets n → Meets n
removeRedundancies [] = []
removeRedundancies (M ∷ Ms) with necessary? M Ms
... | yes p = removeDependencies M (removeRedundancies Ms)
... | no ¬p = removeRedundancies Ms

-- If we have that M′ is necessary in Ms, then it is still
-- necessary if we remove its dependencies
Necessary-rmDep : ∀ {n} (M M′ : VS n) → M ⊈ M′
                → (Ms : Meets n) 
                → Necessary M′ Ms → Necessary M′ (removeDependencies M Ms)
Necessary-rmDep M′ M M⊈M′ []        []       = M⊈M′ ∷ []
Necessary-rmDep M′ M M⊈M′ (M″ ∷ Ms) (n ∷ ns) with M′ ⊆? M″
... | yes p = Necessary-rmDep M′ M M⊈M′ Ms ns
... | no ¬p = n ∷ (Necessary-rmDep M′ M M⊈M′ Ms ns)

-- Similarly, if M′ is necessary we can remove all redunancies
-- (and their dependencies), and M′ is still necessary
Necessary-rmReds : ∀ {n} (M′ : VS n) (Ms : Meets n) 
                     → Necessary M′ Ms → Necessary M′ (removeRedundancies Ms)
Necessary-rmReds M′ []       []       = []
Necessary-rmReds M′ (M ∷ Ms) (n ∷ ns) with necessary? M Ms
... | yes p = Necessary-rmDep M M′ n (removeRedundancies Ms) (Necessary-rmReds M′ Ms ns)
... | no ¬p = Necessary-rmReds M′ Ms ns

-- If M′ is redundant (∃ λ M → M ⊆ M′), then we can safely 
-- remove it without changing the evaluated value.
-- The lemma₅ uses absorption
rmRed-correct : ∀ {n} (Γ : Env n) {M M′}
                → M ⊆ M′ 
                → ⟦ M ⟧″ Γ ∨ ⟦ M′ ⟧″ Γ ≈ ⟦ M ⟧″ Γ
rmRed-correct []      stop                       = ∨-idempotent ⊤
rmRed-correct (γ ∷ Γ) (keep-T {_} {M} {M′} M⊆M′) = lemma₄ (rmRed-correct Γ M⊆M′)
rmRed-correct (γ ∷ Γ) (keep-N {_} {M} {M′} M⊆M′) = lemma₄ (rmRed-correct Γ M⊆M′)
rmRed-correct (γ ∷ Γ) (drop T {_} {M} {M′} M⊆M′) = lemma₅ (rmRed-correct Γ M⊆M′)
rmRed-correct (γ ∷ Γ) (drop N {_} {M} {M′} M⊆M′) = lemma₅ (rmRed-correct Γ M⊆M′)
rmRed-correct (γ ∷ Γ) (drop F {_} {M} {M′} M⊆M′) = lemma₄ (rmRed-correct Γ M⊆M′)

-- If a meet is necessary, we can safely remove all its dependencies 
rmDep-correct : ∀ {n} (Γ : Env n) M′ Ms
              → Necessary M′ Ms
              → ⟦ M′ ⟧″ Γ ∨ ⟦ Ms ⟧′ Γ ≈ ⟦ removeDependencies M′ Ms ⟧′ Γ
rmDep-correct Γ M′ []       [] = refl 
rmDep-correct Γ M′ (M ∷ Ms) (n ∷ ns) with M′ ⊆? M
... | yes p = sym (∨-assoc _ _ _) 
            ⟨ trans ⟩ (rmRed-correct Γ p ⟨ ∨-cong ⟩ refl) 
            ⟨ trans ⟩ rmDep-correct Γ M′ Ms ns
... | no ¬p = lemma₆ ⟨ trans ⟩ (refl ⟨ ∨-cong ⟩ rmDep-correct Γ M′ Ms ns) 

-- If a meet is redundant, we can safely remove it
rmRedMeet-correct : ∀ {n} (Γ : Env n) M′ {Ms}
            → Redundant M′ Ms
            → ⟦ M′ ⟧″ Γ ∨ ⟦ Ms ⟧′ Γ ≈ ⟦ Ms ⟧′ Γ
rmRedMeet-correct Γ M′ (M , here ≡-refl , M⊆M′) = lemma₆ ⟨ trans ⟩ sym (∨-assoc _ _ _) ⟨ trans ⟩ (rmRed-correct Γ M⊆M′ ⟨ ∨-cong ⟩ refl)
rmRedMeet-correct Γ M′ (M , there M∈Ms  , M⊆M′) = lemma₆ ⟨ trans ⟩ (refl ⟨ ∨-cong ⟩ rmRedMeet-correct Γ M′ (M , M∈Ms , M⊆M′))
  
-- Removing all redundancies from meets does not change the value
rmReds-correct : ∀ {n} (Γ : Env n) Ms
               → ⟦ Ms ⟧′ Γ ≈ ⟦ removeRedundancies Ms ⟧′ Γ
rmReds-correct Γ []       = refl
rmReds-correct Γ (M ∷ Ms) with necessary? M Ms
... | yes p = refl ⟨ ∨-cong ⟩ rmReds-correct Γ Ms 
            ⟨ trans ⟩ rmDep-correct Γ M (removeRedundancies Ms) 
                                        (Necessary-rmReds M Ms p)
... | no ¬p = rmRedMeet-correct Γ M (¬Necessary→Redundant M Ms ¬p) 
            ⟨ trans ⟩ rmReds-correct Γ Ms
  
       