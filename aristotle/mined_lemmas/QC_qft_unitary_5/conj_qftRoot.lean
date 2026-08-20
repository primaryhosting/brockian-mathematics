/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2πi / N)` used in the QFT. -/

lemma conj_qftRoot (N : ℕ) : (starRingEnd ℂ) (qftRoot N) = (qftRoot N)⁻¹ := by
  rw [qftRoot, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff, neg_div]

/-- Orthogonality of the columns of the DFT matrix. -/
