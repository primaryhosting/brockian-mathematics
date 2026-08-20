/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
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

/-- The primitive `32`-nd root of unity used by the 5-qubit quantum Fourier transform. -/

lemma conj_qftOmega5_pow (m : ℕ) :
    (starRingEnd ℂ) (qftOmega5 ^ m) = (qftOmega5 ^ m)⁻¹ := by
  have h : ‖qftOmega5 ^ m‖ = 1 := by
    rw [norm_pow, qftOmega5_norm, one_pow]
  rw [Complex.inv_eq_conj h]

/-- Orthogonality relations for the columns of the QFT matrix. -/
