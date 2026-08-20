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

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

noncomputable def P19 : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.of fun j k => zeta19 ^ (j.val * k.val)

/-- The conjugate Fourier matrix (the inverse of `P19` up to the factor `19`). -/
