import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
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

/-- The planar rotation matrix by an angle `t`. -/

lemma rot_add_two_pi_mul (t : ℝ) (k : ℕ) : rot (t + k * (2 * Real.pi)) = rot t := by
  simp only [rot]
  rw [show ((k : ℝ)) = ((k : ℤ) : ℝ) by push_cast; ring, Real.cos_add_int_mul_two_pi,
    Real.sin_add_int_mul_two_pi]

/-- The angle attached to the vertex `i` of the regular `n`-gon. -/
