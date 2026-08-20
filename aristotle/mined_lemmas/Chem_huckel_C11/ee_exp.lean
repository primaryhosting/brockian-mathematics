import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

lemma ee_exp (k : Fin 11) : ee k = Complex.exp (((2 * Real.pi * (k : ℕ) / 11 : ℝ) : ℂ) * I) := by
  unfold ee zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

