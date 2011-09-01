
--------------------------------------------------------------------------------
-- A library and DSL to describe Algebraic structures
-- Dan Rosén
--------------------------------------------------------------------------------

module Algebra.README where

-- The motivation to start this DSL was the fact that the way of expressing
-- algebraic structures in the Agda Standard Library contains a myriad of
-- records and duplicate work. This project was intended to express this in 
-- a simpler way. It was however abandoned due of extreme typechecking times,
-- but remains as a nice artifact of using some Agda type hackery of polyvariadic
-- builder functions, with lambda functions with mixfix arguments.

-- Examples how the DSL is used to describe different structures.
import Algebra.Instance

-- Example how a Commutative Semiring is instantiated
import Algebra.Test

