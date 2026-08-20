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

open Polynomial

/-- A primitive 8-th root of unity. -/

noncomputable def huckelEigenvalue (k : Fin 8) : ℝ := 2 * Real.cos (2 * Real.pi * k.val / 8)

/-- The (unnormalised) discrete Fourier matrix of size 8. -/
