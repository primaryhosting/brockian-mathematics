import Mathlib

/-!
# Sum Omega Pow
Category: Characters
Target: Brockian.Characters5.sum_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian
namespace Characters5

/-- A primitive 5th root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

@[inherit_doc] scoped notation "ω" => Brockian.Characters5.omega

/-- `ω` is a primitive 5th root of unity. -/
theorem isPrimitiveRoot_omega : IsPrimitiveRoot ω 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega, mul_comm, mul_assoc, mul_left_comm] using h

/-- The sum of all five 5th roots of unity vanishes. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, ω ^ k = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

end Characters5
end Brockian

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

