import Mathlib

/-!
# Hwin Nonneg Iff Threshold
Category: A Assembly
Target: Zeta23Scaffold.Hwin_nonneg_iff_threshold
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- On `0 < λ ≤ 1`, the window function is nonnegative exactly when `λ ≥ 3 - √6`
(the degeneration threshold `3 - √6 = 0.5505...`).

Proof route: multiplying by `3λ > 0`, `0 ≤ H λ` is equivalent to `λ² - 6λ + 3 ≤ 0`,
whose roots are `3 ± √6`; since `λ ≤ 1 < 3 + √6`, this reduces to `λ ≥ 3 - √6`. -/
theorem Hwin_nonneg_iff_threshold (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 1) :
    0 ≤ Hwin lam ↔ 3 - Real.sqrt 6 ≤ lam := by
  have h6 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have hlt : Real.sqrt 6 < 3 := by nlinarith
  have hgt : 2 < Real.sqrt 6 := by nlinarith
  have hinv : 1 / lam * lam = 1 := by field_simp
  have key : Hwin lam * (3 * lam) = -(lam ^ 2 - 6 * lam + 3) := by
    simp only [Hwin]
    field_simp
    ring
  constructor
  · intro h
    have hq : lam ^ 2 - 6 * lam + 3 ≤ 0 := by
      nlinarith [mul_nonneg h (by positivity : (0:ℝ) ≤ 3 * lam)]
    nlinarith
  · intro h
    have hq : lam ^ 2 - 6 * lam + 3 ≤ 0 := by nlinarith
    nlinarith [key, hpos]

end Zeta23Scaffold

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

