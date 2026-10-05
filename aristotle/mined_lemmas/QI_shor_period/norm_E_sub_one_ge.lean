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

theorem norm_E_sub_one_ge (x : ℝ) (hx : |x| ≤ 5 * Real.pi / 4) :
    (2 / 5) * |x| ≤ ‖E x - 1‖ := by
  rw [norm_E_sub_one]
  have hpi := Real.pi_pos
  have hy : |x| / 2 ≤ Real.pi := by linarith
  have hs0 : 0 ≤ Real.sin (|x| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hy
  have habs : |Real.sin (x / 2)| = Real.sin (|x| / 2) := by
    rcases le_or_gt 0 x with h | h
    · have hx' : |x| = x := abs_of_nonneg h
      rw [hx'] at hs0 ⊢
      exact abs_of_nonneg hs0
    · have hx' : |x| = -x := abs_of_neg h
      rw [hx'] at hs0 ⊢
      rw [show -x / 2 = -(x / 2) by ring, Real.sin_neg] at hs0 ⊢
      exact abs_of_nonpos (by linarith)
  rw [habs]
  have h1 : (2 / 5) * (|x| / 2) ≤ Real.sin (|x| / 2) := by
    refine sin_ge_two_fifths_mul _ (by positivity) ?_
    linarith
  linarith

/-! ## A lower bound for exponential sums -/

/-- If the total phase spread `A * |θ|` is at most `5π/4`, the geometric exponential sum
has norm at least `(2/5) A`. -/
