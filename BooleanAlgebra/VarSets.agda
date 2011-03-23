{-# OPTIONS --universe-polymorphism #-}
module BooleanAlgebra.VarSets where

open import Data.Nat hiding (_<_ ; compare)
open import Data.Vec hiding (drop ; _∈_ ; map ; [_])
open import Data.Fin hiding (_<_ ; compare)
open import Data.List hiding (replicate ; drop)
open import Data.List.Any as Any hiding (tail ; map)
open Any.Membership-≡ hiding (_⊆_ ; _⊈_)
open import Data.ParallelList renaming (tail to Par-tail)
open import Data.Product hiding (map)
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Data.Sum

open import BooleanAlgebra.Member

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Maybe

open import Relation.Binary.List.StrictLex as Lex

MemberListLexOrder : StrictTotalOrder _ _ _
MemberListLexOrder = <-strictTotalOrder Member-Order 

open StrictTotalOrder MemberListLexOrder using (compare)

VS : ℕ → Set
VS = Vec Member

singleton : ∀ {n} → Fin n → VS n
singleton zero    = T ∷ replicate F
singleton (suc n) = F ∷ singleton n


_∩_ : ∀ {n} → VS n → VS n → Maybe (VS n)
[]       ∩ []       = just []
(x ∷ xs) ∩ (y ∷ ys) with (x ⋀ y) | (xs ∩ ys)
... | just v | just vs = just (v ∷ vs)
... | _      | _       = nothing

private
  ∩-lemma : ∀ {n} v v′ → (vs vs′ : VS n) → (v ∷ vs) ∩ (v′ ∷ vs′) ≡ nothing → vs ∩ vs′ ≡ nothing ⊎ v ⋀ v′ ≡ nothing
  ∩-lemma v v′ vs vs′ eq with v ⋀ v′ | vs ∩ vs′
  ∩-lemma v v′ vs vs′ () | just v″ | just vs″
  ... | nothing | just vs″ = inj₂ refl
  ... | _       | nothing  = inj₁ refl

  jn : ∀ {A : Set} {x : Maybe A} {v : A} → x ≡ nothing → x ≡ just v → ∀ {Whatever : Set} → Whatever
  jn {x = just _} () eq
  jn {x = nothing}  eq ()

∩-nothing : ∀ {n} → (vs vs′ : VS n) → vs ∩ vs′ ≡ nothing → ∃ λ i → lookup i vs  ⋀ lookup i vs′ ≡ nothing
∩-nothing [] [] ()
∩-nothing (x ∷ xs) (y ∷ ys) eq with inspect (x ⋀ y)
... | nothing with-≡ eq′ = zero , eq′
... | just v  with-≡ eq′ with ∩-lemma x y xs ys eq
... | inj₂ eq″ = jn eq″ eq′
... | inj₁ eq″ with ∩-nothing xs ys eq″
... | i , eq‴ = suc i , eq‴

⋀-nothing : ∀ x y → x ⋀ y ≡ nothing → (x ≡ T × y ≡ N) ⊎ (x ≡ N × y ≡ T)
⋀-nothing T T = λ ()
⋀-nothing T N = λ x' → inj₁ (refl , refl)
⋀-nothing T F = λ ()
⋀-nothing N T = λ x' → inj₂ (refl , refl)
⋀-nothing N N = λ ()
⋀-nothing N F = λ ()
⋀-nothing F T = λ ()
⋀-nothing F N = λ ()
⋀-nothing F F = λ ()

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
  keep-T : ∀ {n}   {xs ys : VS n} → xs ⊆ ys → (T ∷ xs) ⊆ (T ∷ ys)
  keep-N : ∀ {n}   {xs ys : VS n} → xs ⊆ ys → (N ∷ xs) ⊆ (N ∷ ys)
  drop   : ∀ {n} x {xs ys : VS n} → xs ⊆ ys → (F ∷ xs) ⊆ (x ∷ ys)

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

-- We have meets : M₁ ∧ M₂ ∧ ... ∧ Mn
-- M′ is redundant if ∃ i . Mi ⊆ M′
-- We say M′ is necessary if ∀ i . Mi ⊈ M′

Necessary : ∀ {n} → VS n → Meets n → Set
Necessary M′ Ms = ParList (λ M → M ⊈ M′) Ms

Redundant : ∀ {n} → VS n → Meets n → Set
Redundant M′ Ms = ∃ λ M → M ∈ Ms × M ⊆ M′

-- As expected, they are inverses of each other.
¬Necessary→Redundant : ∀ {n} (M′ : VS n) (Ms : Meets n) → ¬ (Necessary M′ Ms) → Redundant M′ Ms
¬Necessary→Redundant M′ []       ¬Nec = ⊥-elim (¬Nec [])
¬Necessary→Redundant M′ (M ∷ Ms) ¬Nec with M ⊆? M′
... | yes p = M , here refl , p
... | no ¬p with ¬Necessary→Redundant M′ Ms (λ ¬ps → ¬Nec (¬p ∷ ¬ps))
... | M' , M'∈Ms , M'⊆M′ = M' , there M'∈Ms , M'⊆M′

¬Redundant→Necessary : ∀ {n} (M′ : VS n) (Ms : Meets n) → ¬ (Redundant M′ Ms) → Necessary M′ Ms
¬Redundant→Necessary M′ []       ¬Red = []
¬Redundant→Necessary M′ (M ∷ Ms) ¬Red = (λ M⊆M′ → ¬Red (M , here refl , M⊆M′)) 
                                      ∷ ¬Redundant→Necessary M′ Ms 
                                              (λ xs → ¬Red ( proj₁ xs
                                                           , there (proj₁ (proj₂ xs)) 
                                                           , proj₂ (proj₂ xs)))

Redundant∧Necessary→⊥ : ∀ {n} (M′ : VS n) (Ms : Meets n) → Redundant M′ Ms → Necessary M′ Ms → ⊥
Redundant∧Necessary→⊥ M′ []       (_ , () , _)         Nec
Redundant∧Necessary→⊥ M′ (M ∷ Ms) (.M , here refl , M⊆M′)  (p ∷ ps) = p M⊆M′
Redundant∧Necessary→⊥ M′ (M ∷ Ms) (M' , there pxs , M'⊆M′) (p ∷ ps) = 
  Redundant∧Necessary→⊥ M′ Ms (M' , pxs , M'⊆M′) ps

necessary? : ∀ {n} → Decidable (Necessary {n})
necessary? M′ []       = yes []
necessary? M′ (M ∷ Ms) with M ⊆? M′
... | yes p = no (Redundant∧Necessary→⊥ M′ (M ∷ Ms) (M , here refl , p))
... | no ¬p with necessary? M′ Ms
... | yes p′ = yes (¬p ∷ p′)
... | no ¬p′ = no (¬p′ ∘ Par-tail)

-- To insert in the set of meets:
-- Check if the set is necessary.
-- If it is, remove the set that are redundant because of this set.
-- Then insert in in the set (notice order matter or normal forms will be different)

removeRedundant : ∀ {n} → VS n → Meets n → Meets n
removeRedundant M′ []       = []
removeRedundant M′ (M ∷ Ms) with M′ ⊆? M
... | yes p = removeRedundant M′ Ms
... | no ¬p = M ∷ removeRedundant M′ Ms

setInsert : ∀ {n} → VS n → Meets n → Meets n
setInsert M′ [] = [ M′ ] 
setInsert M′ (M ∷ Ms) with compare (toList M′) (toList M)
... | tri> _ _ _ = M ∷ setInsert M′ Ms
... | _          = M′ ∷ M ∷ Ms  -- Hmm, equality cannot happen... it could be proven here

insert : ∀ {n} → VS n → Meets n → Meets n
insert M′ Ms with necessary? M′ Ms 
... | yes p = setInsert M′ (removeRedundant M′ Ms)
... | no ¬p = Ms

-- Union of two meets
_⋃_ : ∀ {n} → Meets n → Meets n → Meets n
_⋃_ (M ∷ Ms) Ms′ = insert M (Ms ⋃ Ms′)
_⋃_ []       Ms′ = Ms′

