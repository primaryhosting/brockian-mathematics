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

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₈`. -/

lemma om_prim : IsPrimitiveRoot om 8 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 8 (by norm_num)

/-- `ωᵏ + ω⁻ᵏ = 2 cos (2πk/8)`. -/
