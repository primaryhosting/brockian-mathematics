/-
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: in this Lean/Mathlib toolchain a module docstring (`/-! ... -/`) may not precede the
-- `import` line, so the header appears at the top of the file as a plain block comment and is
-- repeated verbatim as the module docstring immediately after the import.

open Set

namespace Math

/-- **Lagrange's Mean Value Theorem.**
If `f : ℝ → ℝ` is differentiable on the closed interval `[a, b]` (with `a < b`), then there is
a point `c` in the open interval `(a, b)` at which `deriv f c = (f b - f a) / (b - a)`.

This is a direct consequence of Mathlib's `exists_deriv_eq_slope`, which assumes only continuity
on `[a, b]` together with differentiability on `(a, b)`. -/

theorem mean_value_of_continuousOn {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hfc hfd

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

