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

lemma abs_zeta (n : ℕ) : ‖zeta n‖ = 1 := by
  rw [zeta, Complex.norm_exp]
  simp [Complex.div_re, Complex.mul_re]

