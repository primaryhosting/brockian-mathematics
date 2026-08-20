import Mathlib

/-!
# Class Number Formula
Category: Frontier Math
Target: Math2.class_number_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology NumberField NumberField.InfinitePlace NumberField.Units

open scoped Real

namespace Math2

variable (K : Type*) [Field K] [NumberField K]

/-- The explicit constant appearing in the analytic class number formula:
`(2 ^ r₁ * (2π) ^ r₂ * R_K * h_K) / (w_K * √|d_K|)`. -/

theorem eq_classNumberConstant_of_tendsto {L : ℂ}
    (hL : Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 L)) :
    L = (classNumberConstant K : ℂ) :=
  tendsto_nhds_unique hL (class_number_formula K)

end Math2

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

