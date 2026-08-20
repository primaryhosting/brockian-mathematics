/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- A primitive `16`-th root of unity, `exp (2πi/16)`. -/

lemma star_omega16_pow (n : ℕ) : star (omega16 ^ n) = (omega16 ^ n)⁻¹ := by
  have h : star (omega16 ^ n) = (starRingEnd ℂ) (omega16 ^ n) := rfl
  rw [h, ← Complex.inv_eq_conj]
  simp [norm_omega16]

/-- Orthogonality relation for the `16`-th roots of unity. -/
