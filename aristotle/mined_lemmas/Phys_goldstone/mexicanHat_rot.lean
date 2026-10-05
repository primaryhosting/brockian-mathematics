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

theorem mexicanHat_rot (t : ℝ) (p : ℝ × ℝ) : mexicanHat (rot t p) = mexicanHat p := by
  have h := Real.sin_sq_add_cos_sq t
  have key : (Real.cos t * p.1 - Real.sin t * p.2) ^ 2
      + (Real.sin t * p.1 + Real.cos t * p.2) ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by nlinarith [h]
  show ((Real.cos t * p.1 - Real.sin t * p.2) ^ 2
      + (Real.sin t * p.1 + Real.cos t * p.2) ^ 2 - 1) ^ 2 = (p.1 ^ 2 + p.2 ^ 2 - 1) ^ 2
  rw [key]

