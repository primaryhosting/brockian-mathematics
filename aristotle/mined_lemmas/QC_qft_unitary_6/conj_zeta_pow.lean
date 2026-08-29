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

lemma conj_zeta_pow (n m : ℕ) :
    (starRingEnd ℂ) (zeta n ^ m) = (zeta n ^ m)⁻¹ := by
  rw [← Complex.inv_eq_conj]
  rw [norm_pow, abs_zeta, one_pow]

/-- Geometric sum of an `n`-th root of unity different from `1` vanishes. -/
