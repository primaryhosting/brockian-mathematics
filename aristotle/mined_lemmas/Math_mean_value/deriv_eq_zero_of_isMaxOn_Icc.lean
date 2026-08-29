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

A self-contained development of the mean value theorem: the interior extremum
principle gives Rolle's theorem, and Rolle's theorem applied to an auxiliary
function gives the mean value theorem.
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

namespace Math

open Set

/-- If `f` attains a maximum over `[a, b]` at an interior point `x`, its derivative
there vanishes. -/

theorem deriv_eq_zero_of_isMaxOn_Icc {f : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ Ioo a b)
    (hmax : IsMaxOn f (Icc a b) x) : deriv f x = 0 :=
  (hmax.isLocalMax (Icc_mem_nhds hx.1 hx.2)).deriv_eq_zero

/-- If `f` attains a minimum over `[a, b]` at an interior point `x`, its derivative
there vanishes. -/
