/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix, whose
`(j, k)` entry is `exp(2πi·jk/N) / √N`. -/

private lemma conj_phase (N n : ℕ) :
    (starRingEnd ℂ) (2 * Real.pi * Complex.I * (n : ℕ) / N)
      = -(2 * Real.pi * Complex.I * (n : ℕ) / N) := by
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
    Complex.conj_natCast]
  ring

/-- Orthogonality of characters: the sum of `exp(2πi·i·m/N)` over `i < N` is `N` when
`N ∣ m` and `0` otherwise. -/
