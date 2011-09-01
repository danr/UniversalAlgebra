
-----------------------------------------------------------------------------------
-- A library for automatically infering equality proofs of Distributive Lattices
-- Dan Rosén
-----------------------------------------------------------------------------------

-- This file gives a brief overview of the components of the solver.

module DLSolver.README where

--
-- Definition: Distributive Lattice (DL), a set with two binary operations 
-- meet and join, commonly _∧_ and _∨_, which are associative, commutative
-- idempotent and absorptive and distributive over each other.
--
-- The solver works by rewriting formulas written in the language of DLs 
-- (Distributive Lattices) in normal forms represented as the free DL of
-- the variables. The normal form is
--
--    M₁ ∨ M₂ ∨ ⋯ ∨ Mn
--
-- where each Mi is a finite meets of variables: 
--
--    Mi = x₁ ∧ x₂ ∧ ⋯ ∧ xm
--
-- The meets and its components should be viewed as sets because of 
-- commutativity and idempotency: 
--
--    { M₁ , M₂ , ⋯ , Mn }, where Mi = { x₁ , x₂ , ⋯ , xm }
--
-- Futhermore, some meets are redundant: we want them to form an antichain.
-- A Meet Mk is redundant if there is a set Mj such that Mj ⊂ Mk, then the
-- meet of Mj will be below the meet of Mk, so we can safely remove the
-- redundant set Mk.



-- First, the expression datatype is defined, and the way to transform it
-- to Disjunctive Normal Form, which is just a nonempty list of meets.
import DLSolver.DNF

-- The meets are presented as these variable sets used
import DLSolver.VarSets

-- Proof that rewriting to DNF preserves semantics of the expression
import DLSolver.DNF-Correct

-- Secondly, after DNF, all redundant sets are removed
import DLSolver.Redundancies

-- Finally, the result is sorted to simulate a set
import DLSolver.Sort

-- The solver is packed here. Uses the reflection primives.
-- Note that by simulating sets by sorting, and using variable sets, we can
-- reflect the obtained definitional equality into a reflexivity proof.
import DLSolver.Solver

-- Examples
import DLSolver.Examples

-- Some lemmas needed
import DLSolver.Lemmas