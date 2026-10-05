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

/-- On `0 < λ ≤ 1`, `H(λ) ≥ 0` iff `λ ≥ 3 - √6`. -/
theorem Hwin_nonneg_iff_threshold (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 1) :
    0 ≤ Hwin lam ↔ 3 - Real.sqrt 6 ≤ lam := by
  have h6 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hlt3 : Real.sqrt 6 < 3 := by
    nlinarith [Real.sqrt_nonneg 6, h6]
  have hgt2 : 2 < Real.sqrt 6 := by
    nlinarith [Real.sqrt_nonneg 6, h6]
  have hinv : 1 / lam * lam = 1 := by
    field_simp
  constructor
  · intro h
    have h' : 0 ≤ (2 - 1 / lam - lam / 3) * (3 * lam) := by
      have := mul_nonneg h (by positivity : (0:ℝ) ≤ 3 * lam)
      simpa [Hwin] using this
    have hq : lam ^ 2 - 6 * lam + 3 ≤ 0 := by nlinarith [hinv]
    nlinarith [Real.sqrt_nonneg 6, h6]
  · intro h
    have hq : lam ^ 2 - 6 * lam + 3 ≤ 0 := by
      nlinarith [Real.sqrt_nonneg 6, h6]
    have : 0 ≤ 2 - 1 / lam - lam / 3 := by nlinarith [hinv, hpos]
    simpa [Hwin] using this

end Zeta23Scaffold

