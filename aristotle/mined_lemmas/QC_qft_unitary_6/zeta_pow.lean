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

lemma zeta_pow (n : ℕ) (m : ℕ) :
    zeta n ^ m = Complex.exp (2 * Real.pi * Complex.I * m / n) := by
  rw [zeta, ← Complex.exp_nat_mul]
  ring_nf

