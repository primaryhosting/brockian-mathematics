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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open NormedSpace

/-- In a complex Banach algebra, `exp (x + y) = exp x * exp y` for commuting `x`, `y`. -/

theorem norm_heisenberg_le (H : 𝒜) (hH : IsSelfAdjoint H) (t : ℝ) (A : 𝒜) :
    ‖heisenberg H t A‖ ≤ ‖A‖ := by
  have h1 : ‖propagator H t‖ = 1 := norm_propagator H hH t
  have h2 : ‖propagator H (-t)‖ = 1 := norm_propagator H hH (-t)
  calc ‖heisenberg H t A‖ ≤ ‖propagator H t * A‖ * ‖propagator H (-t)‖ := norm_mul_le _ _
    _ ≤ (‖propagator H t‖ * ‖A‖) * ‖propagator H (-t)‖ := by
        gcongr; exact norm_mul_le _ _
    _ = ‖A‖ := by rw [h1, h2]; ring

/-- Short-time bound: the evolved observable stays close to itself for short times. -/
