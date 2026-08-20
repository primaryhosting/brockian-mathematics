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

/-- The `N`-dimensional quantum Fourier transform matrix:
`(QFT_N)_{j,k} = exp(2πi·j·k/N) / √N`. -/

lemma zeta_pow (N : ℕ) (d : ℤ) (m : ℕ) :
    (zeta N d) ^ m = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * (d : ℂ)) / (N : ℂ)) := by
  rw [zeta, ← Complex.exp_nat_mul]
  congr 1
  ring

