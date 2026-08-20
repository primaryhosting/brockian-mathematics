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

theorem Hwin_nonneg_iff_threshold (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 1) :
    0 ≤ Hwin lam ↔ 3 - Real.sqrt 6 ≤ lam := by
  have h6 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hlt : Real.sqrt 6 < 3 := by
    nlinarith [Real.sqrt_nonneg 6, h6]
  have hgt : 2 < Real.sqrt 6 := by
    nlinarith [Real.sqrt_nonneg 6, h6]
  have hH : Hwin lam = (- (lam ^ 2 - 6 * lam + 3)) / (3 * lam) := by
    rw [Hwin]
    field_simp
    ring
  rw [hH]
  rw [le_div_iff₀ (by positivity)]
  constructor
  · intro h
    nlinarith [Real.sqrt_nonneg 6, h6]
  · intro h
    nlinarith [Real.sqrt_nonneg 6, h6]

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

