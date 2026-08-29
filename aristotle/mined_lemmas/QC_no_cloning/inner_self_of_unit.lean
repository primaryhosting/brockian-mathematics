import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Auxiliary: from an orthonormal pair `a, b` we build the unit vector
`(3/5) • a + (4/5) • b`, whose inner product with `a` is `3/5`. -/

lemma inner_self_of_unit (a : H) (ha : ‖a‖ = 1) : inner ℂ a a = 1 := by
  rw [inner_self_eq_norm_sq_to_K, ha]
  norm_num

