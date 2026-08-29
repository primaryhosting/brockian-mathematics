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

noncomputable def rot : ℝ → ℝ × ℝ → ℝ × ℝ :=
  fun t p => (Real.cos t * p.1 - Real.sin t * p.2, Real.sin t * p.1 + Real.cos t * p.2)

/-- The infinitesimal generator `(x, y) ↦ (-y, x)` of the rotation flow. -/
