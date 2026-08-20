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

import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

lemma sqrt_two_pow_ne_zero (n : ℕ) : ((Real.sqrt (2 ^ n) : ℝ) : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < Real.sqrt (2 ^ n) := Real.sqrt_pos.mpr (by positivity)
  exact_mod_cast h.ne'

/-- **The `n`-qubit quantum Fourier transform matrix is unitary.** -/
