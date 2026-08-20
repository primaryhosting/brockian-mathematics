import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₅`, i.e. the Hückel matrix of
cyclopentadienyl (with `α = 0`, `β = 1`). -/

noncomputable def C5 : Matrix (Fin 5) (Fin 5) ℝ := (SimpleGraph.cycleGraph 5).adjMatrix ℝ

/-- Explicit description of the adjacency matrix of `C₅`. -/
