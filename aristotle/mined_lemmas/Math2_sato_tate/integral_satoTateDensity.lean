/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

namespace Math2

open Filter Topology

/-! ## The Sato–Tate measure -/

/-- The density of the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`. -/

lemma integral_satoTateDensity (a b : ℝ) :
    ∫ x in a..b, satoTateDensity x = satoTateCDF b - satoTateCDF a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    have h1 : HasDerivAt (fun y : ℝ => y - Real.sin y * Real.cos y)
        (1 - (Real.cos x * Real.cos x + Real.sin x * -Real.sin x)) x :=
      (hasDerivAt_id x).sub ((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x))
    have h2 := h1.div_const Real.pi
    convert h2 using 1
    unfold satoTateDensity
    have hpi := Real.pi_ne_zero
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]
  · exact (continuous_satoTateDensity).intervalIntegrable _ _

