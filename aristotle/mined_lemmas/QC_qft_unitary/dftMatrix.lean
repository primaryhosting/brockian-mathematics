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

open Complex

/-- The `N × N` discrete Fourier transform matrix:
`(dftMatrix N) j k = (1/√N) * exp (2πi jk / N)`. -/

noncomputable def dftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    (Real.sqrt N : ℂ)⁻¹ *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / (N : ℂ))

/-- The `n`-qubit quantum Fourier transform matrix, of size `2^n × 2^n`. -/
