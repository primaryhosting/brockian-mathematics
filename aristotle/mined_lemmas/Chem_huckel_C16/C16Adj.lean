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

set_option grind.warning false

namespace Chem

/-- A primitive 16-th root of unity. -/

noncomputable def C16adj : Matrix (Fin 16) (Fin 16) ℂ :=
  (SimpleGraph.cycleGraph 16).adjMatrix ℂ

/-- The predicted Hückel eigenvalues `2 cos (2πk/16)`. -/
