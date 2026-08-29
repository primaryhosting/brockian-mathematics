/-
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` associated to `ω`. -/

theorem geom_sum_ω : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have h := isPrimitiveRoot_ω.geom_sum_eq_zero (by norm_num)
  simp [Finset.sum_range_succ] at h
  linear_combination h

