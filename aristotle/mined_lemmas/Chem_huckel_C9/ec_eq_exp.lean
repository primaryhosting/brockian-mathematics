import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/

lemma ec_eq_exp (k : ZMod 9) :
    ec k = Complex.exp (((2 * Real.pi * k.val / 9 : ℝ) : ℂ) * Complex.I) := by
  rw [ec, zeta9, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `e(k) + e(-k) = 2 cos (2πk/9)`. -/
