import Mathlib

/-!
# Hwin Nonneg Iff Threshold
Category: A Assembly
Target: Zeta23Scaffold.Hwin_nonneg_iff_threshold
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- The window functional `H(λ) = 2 - 1/λ - λ/3`. -/

noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- On `0 < λ ≤ 1`, `H(λ) ≥ 0` iff `λ ≥ 3 - √6`. -/
