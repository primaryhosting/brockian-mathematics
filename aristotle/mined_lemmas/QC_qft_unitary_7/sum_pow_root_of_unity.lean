/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
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

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`F j k = exp (2 π i j k / N) / √N`. -/

lemma sum_pow_root_of_unity {N : ℕ} {η : ℂ} (hη : η ^ N = 1) :
    ∑ m : Fin N, η ^ (m : ℕ) = if η = 1 then (N : ℂ) else 0 := by
  by_cases h : η = 1
  · simp [h]
  · rw [if_neg h, Fin.sum_univ_eq_sum_range (fun m => η ^ m) N, geom_sum_eq h, hη]
    simp

/-- The entries of the QFT matrix in terms of the primitive root `ζ = exp (2 π i / N)`. -/
