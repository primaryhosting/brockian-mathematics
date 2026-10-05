/-
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` with values in `ℂ`. -/

lemma omega_geom_sum : (1 : ℂ) + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have h := omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ] using h

/-- The character values of `e` over all of `ZMod 5` sum to zero. -/
