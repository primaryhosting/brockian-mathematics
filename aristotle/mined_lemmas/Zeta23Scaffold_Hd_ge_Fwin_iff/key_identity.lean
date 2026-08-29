/-
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- `Hwin lam = 2 - 1/lam - lam/3`. -/

lemma key_identity {lam : ℝ} (hlam : 0 < lam) :
    6 * lam * (3 + lam ^ 2) * (Hd lam - Fwin lam)
      = (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  have h2 : (1 : ℝ) + lam ^ 2 / 3 ≠ 0 := ne_of_gt (denom_pos lam)
  simp only [Hd, Hwin, Fwin]
  field_simp
  ring

/-- The equivalence `F(λ) ≤ H_d(λ) ↔ 0 ≤ H(λ)`, valid for every `λ > 0`. -/
