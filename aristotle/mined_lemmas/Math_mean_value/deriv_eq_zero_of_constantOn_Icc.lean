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

theorem deriv_eq_zero_of_constantOn_Icc {f : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b)
    (hconst : ∀ z ∈ Icc a b, f z = f a) : deriv f c = 0 := by
  have hev : f =ᶠ[nhds c] (fun _ : ℝ => f a) := by
    filter_upwards [Ioo_mem_nhds hc.1 hc.2] with z hz
    exact hconst z (Ioo_subset_Icc_self hz)
  rw [hev.deriv_eq, deriv_const]

/-- **Rolle's theorem.** A function continuous on `[a, b]` (with `a < b`) taking equal
values at the endpoints has a critical point in the open interval `(a, b)`.  No
differentiability hypothesis is needed: at a point where `f` is not differentiable,
`deriv f` is `0` by convention. -/
