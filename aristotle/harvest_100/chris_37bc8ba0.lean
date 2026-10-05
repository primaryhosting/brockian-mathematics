import Mathlib

/-!
# Hwin Nonneg Iff Threshold
Category: A Assembly
Target: Zeta23Scaffold.Hwin_nonneg_iff_threshold
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede any command, including module
-- docstrings, so the required header comment appears immediately after the import.

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Scaffold

/-- The window function `H(λ) = 2 - 1/λ - λ/3`. -/
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- On `0 < λ ≤ 1`, `H(λ) ≥ 0` exactly when `λ ≥ 3 - √6 ≈ 0.5505`. -/
theorem Hwin_nonneg_iff_threshold (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 1) :
    0 ≤ Hwin lam ↔ 3 - Real.sqrt 6 ≤ lam := by
  have h6 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have hlt : Real.sqrt 6 < 3 := by nlinarith
  have hgt : 2 < Real.sqrt 6 := by nlinarith
  have hexp : Hwin lam = (-(lam ^ 2 - 6 * lam + 3)) / (3 * lam) := by
    unfold Hwin
    field_simp
    ring
  rw [hexp, le_div_iff₀ (by linarith)]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

end Zeta23Scaffold

