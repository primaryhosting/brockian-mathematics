/-
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

section Goldstone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Noether / infinitesimal invariance.**  If the potential `V` is invariant under a
one-parameter family of field transformations `Φ t` whose infinitesimal generator at `t = 0`
is the continuous linear map `A`, then the gradient of `V` is everywhere orthogonal to the
direction of the symmetry flow: `dV_x (A x) = 0`. -/

theorem goldstone_mexicanHat :
    ∃ v : ℝ × ℝ, v ≠ 0 ∧ ∀ w : ℝ × ℝ,
      (fderiv ℝ (fderiv ℝ mexicanHat) ((1 : ℝ), (0 : ℝ)) w) v = 0 ∧
      (fderiv ℝ (fderiv ℝ mexicanHat) ((1 : ℝ), (0 : ℝ)) v) w = 0 := by
  refine goldstone mexicanHat contDiff_mexicanHat rotGen rot rot_zero
    (fun t p => mexicanHat_rot t p) hasDerivAt_rot ((1 : ℝ), (0 : ℝ)) fderiv_mexicanHat_vacuum ?_
  simp [rotGen, Prod.ext_iff]

end MexicanHat

end Phys

