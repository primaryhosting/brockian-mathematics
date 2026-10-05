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

theorem mexHatHessian_radial : mexHatHessian ((1 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) = 8 := by
  simp [mexHatHessian]

/-- **Non-vacuity of Goldstone's theorem.**  For the Mexican-hat model, the hypotheses of
`Phys.goldstone_of_infinitesimal_invariance` hold, so the mass matrix at the vacuum
`(1,0)` annihilates the Goldstone direction `(0,1)`, even though the mass matrix itself is
nonzero (the radial mode is massive with `B (1,0) (1,0) = 8`). -/
