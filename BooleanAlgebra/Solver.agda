{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.Solver {β₁ β₂} (BA : BooleanAlgebra β₁ β₂) where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_] ; _>>=_ ; _++_ ; foldr) renaming (map to V-map)
open import Data.List hiding (replicate) renaming (monad to []-monad)
open import Data.Product hiding (map)
open import Data.Maybe

open import Function

open import BooleanAlgebra.Member
open import BooleanAlgebra.VarSets
open import BooleanAlgebra.DNF

open BooleanAlgebra BA renaming (Carrier to X)
import Algebra.Props.BooleanAlgebra as P-BA; open P-BA BA
import BooleanAlgebra.Eval as Eval; open Eval BA
import BooleanAlgebra.Lemmas as Lemmas; open Lemmas BA
import BooleanAlgebra.DNF-Correct as DNF-Correct; open DNF-Correct BA

