import Mathlib
/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the first command in a file, so the required
header comment is placed immediately after the single `import Mathlib` line.)
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- The mass-squared operator (Hessian of the potential) at a field configuration `φ₀`:
the second derivative `D²V(φ₀)`, viewed as a continuous linear map sending a fluctuation
direction to the corresponding linear functional. In the physics normalization the mass
matrix of small fluctuations around `φ₀` is exactly this operator. -/

theorem fderiv_eq_zero_along_orbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → ℝ} {φ₀ : E} {c : ℝ → E}
    (hmin : ∀ x, V φ₀ ≤ V x) (horbit : ∀ t, V (c t) = V φ₀) (t : ℝ) :
    fderiv ℝ V (c t) = 0 := by
  have : IsLocalMin V (c t) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [horbit t]
    exact hmin x
  exact this.fderiv_eq_zero

/-- The potential is twice continuously differentiable, so its differential is differentiable. -/
