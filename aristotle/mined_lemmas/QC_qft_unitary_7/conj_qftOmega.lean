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

lemma conj_qftOmega (N : ℕ) :
    (starRingEnd ℂ) (qftOmega N) = (qftOmega N)⁻¹ := by
  rw [qftOmega, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.ext_iff]
  ring

/-- Geometric sum of powers of `ω^d` vanishes for `0 < d < N`. -/
