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

open Complex Polynomial Matrix

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma zeta_primitive : IsPrimitiveRoot zeta 18 := by
  have := Complex.isPrimitiveRoot_exp 18 (by norm_num)
  convert this using 2

