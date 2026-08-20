/-
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The window function `H(λ) = 2 - 1/λ - λ/3`. -/

lemma Hwin_eq (lam : ℝ) (hlam : 0 < lam) :
    Hwin lam = (6 * lam - 3 - lam ^ 2) / (3 * lam) := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  simp only [Hwin]
  field_simp
  ring

/-- Unconditional form (for all `λ > 0`): `F(λ) ≤ H_d(λ) ↔ 0 ≤ H(λ)`. -/
