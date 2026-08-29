import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
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
set_option pp.letVarTypes true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Infinitesimal (Noether) form of a continuous symmetry.**
If `V` is differentiable and invariant under a one-parameter family of transformations
`Φ t` with `Φ 0 = id` whose velocity field at `t = 0` is `A`, then the gradient of `V`
annihilates the symmetry direction `A x` at every field configuration `x`. -/

theorem mexHat_goldstone :
    ∃ v : ℝ × ℝ, v ≠ 0 ∧ (∀ w : ℝ × ℝ, mexHatHessian v w = 0) ∧
      (∀ w : ℝ × ℝ, mexHatHessian w v = 0) := by
  refine goldstone_of_infinitesimal_invariance (V := mexHatPotential) (A := mexHatGen)
    (x₀ := ((1 : ℝ), (0 : ℝ))) hasFDerivAt_mexHatPotential hasFDerivAt_mexHatGrad
    mexHat_infinitesimal_invariance mexHat_isLocalMin ?_
  simp [mexHatGen, Prod.ext_iff]

/-- In the Mexican-hat model the Goldstone direction is the tangent `(0, 1)` to the vacuum
circle, and it is indeed a zero mode of the mass matrix. -/
