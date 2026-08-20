/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Complex Finset Matrix

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix:
`F i j = exp (2 π i · j / N) / √N`. -/

private lemma exp_root_pow (N : ℕ) (m : ℂ) (k : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * m / N) ^ k
      = Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ) * m) / N) := by
  rw [← Complex.exp_nat_mul]; ring_nf

/-- Orthogonality of characters: the sum of `exp (2 π i k m / N)` over `k < N` vanishes
unless `m = 0` (for `|m| < N`). -/
