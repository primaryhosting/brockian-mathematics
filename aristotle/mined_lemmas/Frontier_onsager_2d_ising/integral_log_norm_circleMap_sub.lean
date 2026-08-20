/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

/-! ## The 2D Ising model on a finite torus -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

theorem integral_log_norm_circleMap_sub (c : ℂ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log ‖circleMap 0 1 θ - c‖
      = 2 * Real.pi * Real.posLog ‖c‖ := by
  have h := circleAverage_log_norm_sub_const_eq_posLog (a := c)
  rw [Real.circleAverage, smul_eq_mul] at h
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  field_simp at h
  linarith [h]

/-- The classical evaluation `∫₀^{2π} log (a - b cos θ) dθ = 2π log ((a + √(a²-b²))/2)`
for `|b| < a`.  It is proved from Mathlib's Jensen-formula machinery, namely
`circleAverage_log_norm_sub_const_eq_posLog`. -/
