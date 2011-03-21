module LatticeSolver.VariableSets where

open import Data.Nat hiding (_<_ ; compare)
open import Data.Vec hiding (drop ; _∈_ ; map ; [_] ; fromList ; toList)
open import Data.Fin hiding (_<_ ; compare)
open import Data.Bool
open import Data.List hiding (replicate ; drop ; [_])
open import Data.List.NonEmpty hiding (tail ; SnocView ; map)
open import Data.List.Any as Any hiding (tail ; map)
open Any.Membership-≡ hiding (_⊆_ ; _⊈_)
open import Data.ParallelList renaming (tail to Par-tail)
open import Data.Product hiding (map)
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)

open import Function

open import Level renaming (zero to z)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

VS : ℕ → Set
VS = Vec Bool

data VS₁ : ℕ → Set where
  true∷_  : ∀ {n} → (xs : VS n) → VS₁ (suc n)
  false∷_ : ∀ {n} → (xs : VS₁ n) → VS₁ (suc n)

singleton : ∀ {n} → Fin n → VS₁ n
singleton zero    = true∷ replicate false
singleton (suc n) = false∷ singleton n

toVS : ∀ {n} → VS₁ n → VS n
toVS (true∷ xs)  = true ∷ xs
toVS (false∷ xs) = false ∷ toVS xs

_∪′_ : ∀ {n} → VS n → VS n → VS n
[]       ∪′ []       = []
(x ∷ xs) ∪′ (y ∷ ys) = (x ∨ y) ∷ xs ∪′ ys

_∪_ : ∀ {n} → VS₁ n → VS₁ n → VS₁ n
(true∷ xs)  ∪ (true∷ ys)  = true∷ (xs ∪′ ys)
(true∷ xs)  ∪ (false∷ ys) = true∷ (xs ∪′ toVS ys)
(false∷ xs) ∪ (true∷ ys)  = true∷ (toVS xs ∪′ ys)
(false∷ xs) ∪ (false∷ ys) = false∷ (xs ∪ ys)

Meets₁ : ℕ → Set
Meets₁ n = List⁺ (VS₁ n)

Meets₁⁻ : ℕ → Set
Meets₁⁻ n = List (VS₁ n)

Meets : ℕ → Set
Meets n = List (VS n)

module Order {n : ℕ} where

  Meets₁-Order : StrictTotalOrder z z z
  Meets₁-Order = record 
      { Carrier = VS₁ n
      ; _≈_ = _≡_ on toVS
      ; _<_ = _<_ on toVS
      ; isStrictTotalOrder = record 
        { isEquivalence = record { refl = refl; sym = sym; trans = trans }
        ; trans = λ {xs} {ys} {zs} → transitive (toVS xs) (toVS ys) (toVS zs)
        ; compare = λ xs ys → (tri (toVS xs) (toVS ys))
        ; <-resp-≈ = (λ {xs} {ys} {zs} ys≡zs xs<ys → subst (_<_ (toVS xs)) ys≡zs xs<ys) 
                   , (λ {xs} {ys} {zs} ys≡zs ys<xs → subst (flip _<_ (toVS xs)) ys≡zs ys<xs)  
        } 
      }
    where
      data _<_ : {n : ℕ} (v₁ v₂ : Vec Bool n) → Set where
        f<t : ∀ {n} (xs ys : Vec Bool n) → (false ∷ xs) < (true ∷ ys)
        eq< : ∀ {n} x {xs ys : Vec Bool n} → (xs<ys : xs < ys) → (x ∷ xs) < (x ∷ ys)
  
      tail< : ∀ {n x} {xs ys : Vec Bool n} → (x ∷ xs) < (x ∷ ys) → xs < ys
      tail< (eq< _ xs<ys) = xs<ys
  
      transitive : ∀ {n} (xs ys zs : Vec Bool n) → xs < ys → ys < zs → xs < zs
      transitive .(false ∷ xs) .(true ∷ ys) .(true ∷ ys') (f<t xs ys) (eq< .true {.ys} {ys'} xs<ys) = f<t xs ys'
      transitive .(false ∷ xs) .(false ∷ ys) .(true ∷ ys') (eq< .false {xs} {ys} xs<ys) (f<t .ys ys') = f<t xs ys'
      transitive .(x ∷ xs) .(x ∷ ys) .(x ∷ ys') (eq< x {xs} {ys} xs<ys) (eq< .x {.ys} {ys'} xs<ys') = eq< x (transitive xs ys ys' xs<ys xs<ys')
  
      tri : ∀ {n} (xs ys : Vec Bool n) → Tri (xs < ys) (xs ≡ ys) (ys < xs)
      tri []           []           = tri≈ (λ ()) refl (λ ())
      tri (true ∷ xs)  (false ∷ ys) = tri> (λ ()) (λ ()) (f<t ys xs)
      tri (false ∷ xs) (true ∷ ys)  = tri< (f<t xs ys) (λ ()) (λ ())
      tri (false ∷ xs) (false ∷ ys) with tri xs ys
      ... | tri<  < ¬≈ ¬> = tri< (eq< false <) (¬≈ ∘ cong tail)     (¬> ∘ tail< ) 
      ... | tri≈ ¬<  ≈ ¬> = tri≈ (¬< ∘ tail<)  (cong (_∷_ false) ≈) (¬> ∘ tail<)
      ... | tri> ¬< ¬≈  > = tri> (¬< ∘ tail<)  (¬≈ ∘ cong tail)     (eq< false >)
      tri (true ∷ xs)  (true ∷ ys) with tri xs ys
      ... | tri<  < ¬≈ ¬> = tri< (eq< true <) (¬≈ ∘ cong tail)    (¬> ∘ tail< ) 
      ... | tri≈ ¬<  ≈ ¬> = tri≈ (¬< ∘ tail<) (cong (_∷_ true) ≈) (¬> ∘ tail<)
      ... | tri> ¬< ¬≈  > = tri> (¬< ∘ tail<) (¬≈ ∘ cong tail)    (eq< true >)
  
  open StrictTotalOrder Meets₁-Order public using (compare)

open Order

data _⊆_ : ∀ {n} → VS n → VS n → Set where
  stop : [] ⊆ []
  keep : ∀ {n}   {xs ys : VS n} → xs ⊆ ys → (true  ∷ xs) ⊆ (true ∷ ys)
  drop : ∀ {n} x {xs ys : VS n} → xs ⊆ ys → (false ∷ xs) ⊆ (x    ∷ ys)

_⊈_ : ∀ {n} → VS n → VS n → Set
A ⊈ B = A ⊆ B → ⊥

tail-⊆ : ∀ {n x y} {xs ys : VS n} → (x ∷ xs) ⊆ (y ∷ ys) → xs ⊆ ys
tail-⊆ (keep y) = y
tail-⊆ (drop _ y) = y

_⊆?_ : ∀ {n} → Decidable (_⊆_ {n})
[]       ⊆? [] = yes stop
(x ∷ xs) ⊆? (y ∷ ys) with xs ⊆? ys
(true  ∷ xs) ⊆? (true  ∷ ys) | yes p = yes (keep p)
(true  ∷ xs) ⊆? (false ∷ ys) | yes p = no λ()
(false ∷ xs) ⊆? (y ∷ ys)     | yes p = yes (drop y p)
(x     ∷ xs) ⊆? (y ∷ ys)     | no ¬p = no (¬p ∘ tail-⊆)

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

removeRedundant : ∀ {n} → VS₁ n → Meets₁⁻ n → Meets₁⁻ n
removeRedundant M′ []       = []
removeRedundant M′ (M ∷ Ms) with toVS M′ ⊆? toVS M
... | yes p = removeRedundant M′ Ms
... | no ¬p = M ∷ removeRedundant M′ Ms

setInsert : ∀ {n} → VS₁ n → Meets₁⁻ n → Meets₁ n
setInsert M′ [] = [ M′ ] 
setInsert M′ (M ∷ Ms) with compare M′ M
... | tri> _ _ _ = M ∷ setInsert M′ Ms
... | _          = M′ ∷ fromList M Ms  -- Hmm, equality cannot happen... it could be proven here

insert : ∀ {n} → VS₁ n → Meets₁ n → Meets₁ n
insert M′ Ms with necessary? (toVS M′) (map toVS (toList Ms))
... | yes p = setInsert M′ (removeRedundant M′ (toList Ms))
... | no ¬p = Ms

-- Union of two meets
union : ∀ {n} → Meets₁ n → Meets₁ n → Meets₁ n
union (M ∷ Ms) Ms′ = insert M (union Ms Ms′)
union [ M ]    Ms′ = M ∷ Ms′