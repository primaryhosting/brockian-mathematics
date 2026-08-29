import Mathlib
/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

namespace Frontier

section Basic

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The inner derivation (adjoint action) `ad H x = H * x - x * H`. -/

lemma norm_ad_le (H x : A) : ‖ad H x‖ ≤ 2 * ‖H‖ * ‖x‖ := by
  have h1 : ‖H * x‖ ≤ ‖H‖ * ‖x‖ := norm_mul_le _ _
  have h2 : ‖x * H‖ ≤ ‖x‖ * ‖H‖ := norm_mul_le _ _
  calc ‖ad H x‖ ≤ ‖H * x‖ + ‖x * H‖ := norm_sub_le _ _
    _ ≤ ‖H‖ * ‖x‖ + ‖x‖ * ‖H‖ := add_le_add h1 h2
    _ = 2 * ‖H‖ * ‖x‖ := by ring

omit [NormedAlgebra ℝ A] in
/-- Each application of the derivation `ad H` costs at most a factor `2‖H‖`. -/
