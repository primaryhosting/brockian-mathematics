-- /-!
-- # Qft Unitary 4
-- Category: Quantum Computing
-- Target: QC.qft_unitary_4
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)
-- -/

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
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

open scoped Matrix

namespace QC

/-- The `N`-point discrete (quantum) Fourier transform matrix:
`(qftMatrix N) j k = N^(-1/2) * exp (2πi·jk/N)`. -/

lemma geom_sum_root_eq_zero {N : ℕ} (hN : 0 < N) {d : ℤ} (hd : ¬ ((N : ℤ) ∣ d)) :
    ∑ m ∈ Finset.range N,
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ m = 0 := by
  rw [geom_sum_eq (root_ne_one hN hd), root_pow_eq_one hN d, sub_self, zero_div]

/-- Orthonormality of the QFT columns: `(qftMatrix N)ᴴ * (qftMatrix N) = 1`. -/
