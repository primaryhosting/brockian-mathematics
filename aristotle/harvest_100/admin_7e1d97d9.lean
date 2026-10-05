/-
# Hwin Nonneg Iff Threshold
Category: A Assembly
Target: Zeta23Scaffold.Hwin_nonneg_iff_threshold
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hwin Nonneg Iff Threshold
Category: A Assembly
Target: Zeta23Scaffold.Hwin_nonneg_iff_threshold
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- `2 < √6 < 3`. -/
theorem sqrt_six_bounds : 2 < Real.sqrt 6 ∧ Real.sqrt 6 < 3 := by
  constructor
  · have : Real.sqrt 4 < Real.sqrt 6 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h4 ▸ this]
  · have : Real.sqrt 6 < Real.sqrt 9 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    have h9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h9 ▸ this]

/-- `H(λ) ≥ 0` iff `λ ≥ 3 - √6 ≈ 0.5505…`, for `0 < λ ≤ 1`. -/
theorem Hwin_nonneg_iff_threshold (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 1) :
    0 ≤ Hwin lam ↔ 3 - Real.sqrt 6 ≤ lam := by
  have h6 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  obtain ⟨hlo, hhi⟩ := sqrt_six_bounds
  have hne : lam ≠ 0 := ne_of_gt hpos
  have h3lam : (0:ℝ) < 3 * lam := by linarith
  have hkey : 0 ≤ Hwin lam ↔ lam ^ 2 - 6 * lam + 3 ≤ 0 := by
    rw [Hwin, show (2 - 1 / lam - lam / 3) = -(lam ^ 2 - 6 * lam + 3) / (3 * lam) by
      field_simp; ring, le_div_iff₀ h3lam]
    constructor <;> intro h <;> nlinarith
  rw [hkey]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

end Zeta23Scaffold

