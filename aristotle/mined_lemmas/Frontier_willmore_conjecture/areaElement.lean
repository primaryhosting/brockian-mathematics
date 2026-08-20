/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
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

/-! ## Basic vector algebra in `ℝ³` -/

/-- Euclidean three-space, as a triple of reals. -/
abbrev R3 := ℝ × ℝ × ℝ

/-- The standard inner product on `ℝ³`. -/

noncomputable def areaElement (X : ℝ → ℝ → R3) (u v : ℝ) : ℝ :=
  nrm3 (cross3 (pd1 X u v) (pd2 X u v))

/-- The mean curvature `H = (eG - 2fF + gE) / (2(EG - F²))` of a parametrized surface,
computed from the coefficients `E, F, G` of the first fundamental form and the coefficients
`e, f, g` of the second fundamental form (taken with respect to the unit normal
`(X_u × X_v)/‖X_u × X_v‖`). -/
