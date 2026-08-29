/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma qftMatrix_apply (n : ℕ) (j k : Fin n) :
    qftMatrix n j k = ((1 / Real.sqrt n : ℝ) : ℂ) * zeta n ^ ((j : ℕ) * (k : ℕ)) := by
  rw [qftMatrix, zeta_pow]
  push_cast
  rfl

