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

/-- `ec n m = exp (2 π i m / n)`, an `n`-th root of unity raised to the power `m`. -/

noncomputable def huckelEnergy (n : ℕ) (k : ℕ) : ℝ :=
  2 * Real.cos (2 * Real.pi * k / n)

/-- The (unnormalised) discrete Fourier transform matrix, whose columns are the Hückel
molecular orbitals of the cycle. -/
