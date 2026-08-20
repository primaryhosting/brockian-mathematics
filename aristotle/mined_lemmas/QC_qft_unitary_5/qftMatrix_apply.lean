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

namespace QC

open Complex Matrix

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

lemma qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k = (1 / Real.sqrt N : ℝ) * zeta N ^ ((j : ℕ) * (k : ℕ)) := by
  have h : (2 * (Real.pi : ℂ) * I * ((j : ℕ) * (k : ℕ)) / N)
      = ((j : ℕ) * (k : ℕ) : ℕ) * (2 * (Real.pi : ℂ) * I / N) := by
    push_cast; ring
  simp only [qftMatrix, zeta, h, Complex.exp_nat_mul]

