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

lemma norm_zeta (n : ℕ) : ‖zeta n‖ = 1 := by
  simp [zeta, Complex.norm_exp]

