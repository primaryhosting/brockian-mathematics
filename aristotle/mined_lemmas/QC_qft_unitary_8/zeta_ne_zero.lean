/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := by
  intro h
  have := norm_zeta n
  rw [h] at this
  simp at this

/-- The key orthogonality relation for the columns of the QFT matrix. -/
