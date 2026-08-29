import Mathlib

/-!
# Repaired Witness Nonneg
Category: Brockian Corpus
Target: Zeta23Obstruction.repaired_witness_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Obstruction

/-- The second factor of the repaired witness kernel is at least `9/10`, since
`Real.cos ≤ 1`. -/
theorem repaired_witness_factor_lower_bound (x : ℝ) :
    (9 : ℝ) / 10 ≤ 1 - (1 / 10) * Real.cos (3 * Real.pi * x) := by
  have h : Real.cos (3 * Real.pi * x) ≤ 1 := Real.cos_le_one _
  linarith

/-- The repaired obstruction witness kernel
`(sin (π x) / (π x))^2 * (1 - (1/10) cos (3 π x))` is nonnegative for every real `x`.
The first factor is a square, hence nonnegative (also at `x = 0`, where the quotient is
junk-valued), and the second factor is at least `9/10 > 0`. -/
theorem repaired_witness_nonneg (x : ℝ) :
    0 ≤ (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 *
        (1 - (1 / 10) * Real.cos (3 * Real.pi * x)) :=
  mul_nonneg (sq_nonneg _)
    (le_trans (by norm_num) (repaired_witness_factor_lower_bound x))

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

