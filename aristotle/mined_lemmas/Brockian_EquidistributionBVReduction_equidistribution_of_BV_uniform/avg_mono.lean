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

/-
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The Cesàro average of `f` along the fractional parts of the sequence `u`. -/

lemma avg_mono (u : ℕ → ℝ) {f g : ℝ → ℝ} (h : ∀ x ∈ Set.Ico (0 : ℝ) 1, f x ≤ g x) (N : ℕ) :
    avg u f N ≤ avg u g N := by
  unfold avg
  have hsum : ∑ n ∈ Finset.range N, f (Int.fract (u n))
      ≤ ∑ n ∈ Finset.range N, g (Int.fract (u n)) := by
    refine Finset.sum_le_sum fun n _ => h _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  gcongr

end Averages

section StepFunctions

