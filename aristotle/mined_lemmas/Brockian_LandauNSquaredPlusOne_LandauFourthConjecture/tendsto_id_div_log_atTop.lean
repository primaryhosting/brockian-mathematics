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

/-
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

/-- A *Landau prime* is a prime of the form `n ^ 2 + 1`. -/

lemma tendsto_id_div_log_atTop :
    Filter.Tendsto (fun x : ℝ => x / Real.log x) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono' Filter.atTop (f₁ := fun x : ℝ => Real.sqrt x / 2)
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hlog : Real.log x ≤ 2 * Real.sqrt x := by
      have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
      have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
        rw [Real.log_sqrt hx0.le]; ring
      nlinarith
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    rw [div_le_div_iff₀ (by norm_num) hlogpos]
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
  · exact Filter.Tendsto.atTop_div_const (by norm_num) Real.tendsto_sqrt_atTop

/-- The Hardy–Littlewood lower bound implies that the counting function is unbounded. -/
