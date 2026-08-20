import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial

/-- The adjacency matrix (Hückel matrix, in units where α = 0 and β = 1) of the cycle
graph `C₃`, over the reals. -/

noncomputable def C3adj : Matrix (Fin 3) (Fin 3) ℝ :=
  (SimpleGraph.cycleGraph 3).adjMatrix ℝ

/-- Explicit form of the adjacency matrix of `C₃`. -/
