/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module doc-comment `/-! ... -/` before `import`,
-- so the required header appears above as an ordinary block comment.)

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Elementary trigonometric estimates -/

/-- A crude but explicit linear lower bound for `sin` on `[0, 5π/8]`. -/

theorem sin_ge_two_fifths_mul (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 5 * Real.pi / 8) :
    (2 / 5) * x ≤ Real.sin x := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  rcases le_or_gt x (Real.pi / 2) with h | h
  · have hs := Real.mul_le_sin h0 h
    have hle : (2 / 5 : ℝ) ≤ 2 / Real.pi := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    nlinarith
  · have hx1 : 0 ≤ x - Real.pi / 2 := by linarith
    have hx2 : x - Real.pi / 2 ≤ Real.pi / 6 := by linarith
    have hcos : Real.cos (Real.pi / 6) ≤ Real.cos (x - Real.pi / 2) :=
      Real.cos_le_cos_of_nonneg_of_le_pi hx1 (by linarith) hx2
    have h6 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
    have h3 : (1.7 : ℝ) ≤ Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0), Real.sqrt_nonneg 3]
    have hsin : Real.sin x = Real.cos (x - Real.pi / 2) := by
      rw [Real.cos_sub_pi_div_two]
    rw [hsin]
    nlinarith

/-! ## The unit-modulus phase function -/

/-- `E t = e^{i t}`. -/
