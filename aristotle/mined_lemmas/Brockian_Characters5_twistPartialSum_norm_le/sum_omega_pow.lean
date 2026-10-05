import Mathlib

/-!
# Twist Partial Sum Norm Le
Category: Characters
Target: Brockian.Characters5.twistPartialSum_norm_le
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

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = e^{2πi/5}`. -/

lemma sum_omega_pow : ∑ j ∈ Finset.range 5, omega ^ j = 0 := by
  have h := geom_sum_mul omega 5
  rw [omega_pow_five, sub_self] at h
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) omega_ne_one

/-- `e` evaluated at the residue of `n` is just `ω ^ n`. -/
