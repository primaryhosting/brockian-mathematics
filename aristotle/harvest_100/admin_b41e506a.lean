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
# Continuum Eq Two Pow Aleph 0
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.continuum_eq_two_pow_aleph0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Continuum Eq Two Pow Aleph 0
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.continuum_eq_two_pow_aleph0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Cardinal

namespace Cardinal

universe u

/-- The cardinality of the power set of `ℕ` is `2 ^ ℵ₀`. -/
theorem mk_set_nat_eq_two_pow_aleph0 : #(Set ℕ) = 2 ^ ℵ₀ := by
  rw [mk_set, mk_nat]

/-- The reals are equinumerous with the power set of `ℕ`. -/
theorem mk_real_eq_mk_set_nat : #ℝ = #(Set ℕ) := by
  rw [mk_real, mk_set_nat_eq_two_pow_aleph0, two_power_aleph0]

/-- The cardinality of the continuum equals `2 ^ ℵ₀`, in universe `0`.

The proof goes through the reals: `𝔠 = #ℝ = #(Set ℕ) = 2 ^ #ℕ = 2 ^ ℵ₀`. -/
theorem continuum_eq_two_pow_aleph0_zero :
    Cardinal.continuum.{0} = 2 ^ Cardinal.aleph0.{0} := by
  rw [← mk_real, mk_real_eq_mk_set_nat, mk_set_nat_eq_two_pow_aleph0]

/-- The cardinality of the continuum equals `2 ^ ℵ₀`, in any universe. -/
theorem continuum_eq_two_pow_aleph0 :
    Cardinal.continuum.{u} = 2 ^ Cardinal.aleph0.{u} := by
  rw [← lift_continuum.{u, 0}, continuum_eq_two_pow_aleph0_zero, lift_two_power, lift_aleph0]

end Cardinal

