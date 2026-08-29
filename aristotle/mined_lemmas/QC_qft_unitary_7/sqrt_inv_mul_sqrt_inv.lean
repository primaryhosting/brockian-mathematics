import Mathlib
/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2πi/N)` used to build the QFT matrix. -/

lemma sqrt_inv_mul_sqrt_inv (N : ℕ) :
    ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ = (N : ℂ)⁻¹ := by
  rw [← mul_inv]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

