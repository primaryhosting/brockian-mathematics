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

namespace QC

/-- The primitive `128`-th root of unity `exp (2 π i / 128)` used by the 7-qubit QFT. -/

noncomputable def qft7 : Matrix (Fin 128) (Fin 128) ℂ :=
  Matrix.of fun j k => omega7 ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt 128 : ℝ)

