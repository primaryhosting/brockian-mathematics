import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

lemma ee_eq_exp (k : ZMod 9) : ee k = Complex.exp ((2 * Real.pi * k.val / 9 : ℝ) * Complex.I) := by
  rw [ee, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The key trigonometric identity: `ω^k + ω^{-k} = 2 cos (2πk/9)`. -/
