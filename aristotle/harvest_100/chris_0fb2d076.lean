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

/-!
# Repaired Witness Nonneg
Category: Brockian Corpus
Target: Zeta23Obstruction.repaired_witness_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Obstruction

/-- The repaired obstruction witness kernel is nonnegative on all of `ℝ`. -/
theorem repaired_witness_nonneg (x : ℝ) :
    0 ≤ (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 *
      (1 - (1 / 10) * Real.cos (3 * Real.pi * x)) := by
  have h1 : (0:ℝ) ≤ (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 := sq_nonneg _
  have h2 : Real.cos (3 * Real.pi * x) ≤ 1 := Real.cos_le_one _
  have h3 : (0:ℝ) ≤ 1 - (1 / 10) * Real.cos (3 * Real.pi * x) := by linarith
  exact mul_nonneg h1 h3

end Zeta23Obstruction

