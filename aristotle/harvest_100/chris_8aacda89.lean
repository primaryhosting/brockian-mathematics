/- Note: Lean requires `import` to be the first command, and a `/-! -/` module
docstring counts as a command, so the requested header is reproduced verbatim
inside a plain (nestable) comment here, and repeated as a module docstring below.

/-!
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial has a root.
Here "nonconstant" is expressed as `0 < p.degree`. This is `Complex.exists_root` in Mathlib. -/
theorem fta_algebra (p : Polynomial ℂ) (hp : 0 < p.degree) : ∃ z : ℂ, p.eval z = 0 :=
  Complex.exists_root hp

/-- Variant of the fundamental theorem of algebra phrased with `natDegree`. -/
theorem fta_algebra' (p : Polynomial ℂ) (hp : p.natDegree ≠ 0) : ∃ z : ℂ, p.eval z = 0 :=
  Complex.exists_root (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hp))

end Math

import Mathlib

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

