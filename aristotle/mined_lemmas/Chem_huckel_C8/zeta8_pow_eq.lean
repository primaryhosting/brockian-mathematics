import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma zeta8_pow_eq (m : ℕ) :
    zeta8 ^ m = Complex.exp ((2 * Real.pi * m / 8 : ℝ) * Complex.I) := by
  rw [zeta8, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

