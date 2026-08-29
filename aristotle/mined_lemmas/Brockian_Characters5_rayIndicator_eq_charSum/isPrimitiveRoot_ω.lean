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

theorem isPrimitiveRoot_ω : IsPrimitiveRoot ω 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  norm_num at h
  exact h

theorem ω_pow_five : ω ^ 5 = 1 := isPrimitiveRoot_ω.pow_eq_one

/-- The five powers of `ω` sum to zero. -/
