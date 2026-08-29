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

theorem hasDerivAt_rot (p : ℝ × ℝ) : HasDerivAt (fun t : ℝ => rot t p) (rotGen p) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => Real.cos t * p.1 - Real.sin t * p.2) (-p.2) 0 := by
    have := ((Real.hasDerivAt_cos 0).mul_const p.1).sub ((Real.hasDerivAt_sin 0).mul_const p.2)
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => Real.sin t * p.1 + Real.cos t * p.2) p.1 0 := by
    have := ((Real.hasDerivAt_sin 0).mul_const p.1).add ((Real.hasDerivAt_cos 0).mul_const p.2)
    simpa using this
  simpa [rot, rotGen] using h1.prodMk h2

