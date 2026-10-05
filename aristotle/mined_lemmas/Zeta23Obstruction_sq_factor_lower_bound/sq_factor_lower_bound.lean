/-
# Sq Factor Lower Bound
Category: Brockian Corpus
Target: Zeta23Obstruction.sq_factor_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sq Factor Lower Bound
Category: Brockian Corpus
Target: Zeta23Obstruction.sq_factor_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Obstruction

/-- The modulation factor `1 - (1/10) * cos (3πx)` is bounded below by `9/10` for every real `x`. -/

theorem sq_factor_lower_bound (x : ℝ) :
    (9 : ℝ) / 10 ≤ 1 - (1 / 10) * Real.cos (3 * Real.pi * x) := by
  have h := Real.cos_le_one (3 * Real.pi * x)
  linarith

end Zeta23Obstruction

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

