/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma exp_two_pi_nat (m : ℕ) : Complex.exp ((2 * Real.pi * m : ℂ) * Complex.I) = 1 := by
  rw [show ((2 * Real.pi * m : ℂ) * Complex.I) = (m : ℂ) * (2 * Real.pi * Complex.I) by ring,
    Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

/-- `ω^m + ω^(18m) = 2 cos (2πm/19)`, the eigenvalue attached to the `m`-th Fourier mode. -/
