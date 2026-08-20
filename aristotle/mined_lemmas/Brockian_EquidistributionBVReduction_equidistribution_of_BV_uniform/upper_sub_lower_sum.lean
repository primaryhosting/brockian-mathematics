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

lemma upper_sub_lower_sum {f : ℝ → ℝ} {m : ℕ} :
    (∑ i ∈ Finset.range m, f (((i : ℝ) + 1) / m)) / m
      - (∑ i ∈ Finset.range m, f ((i : ℝ) / m)) / m = (f (m / m) - f (0 / m)) / m := by
  rw [div_sub_div_same]
  congr 1
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range m, f (((i : ℝ) + 1) / m) - f ((i : ℝ) / m)
      = (fun j : ℕ => f ((j : ℝ) / m)) (i + 1) - (fun j : ℕ => f ((j : ℝ) / m)) i := by
    intro i _; push_cast; ring_nf
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun j : ℕ => f ((j : ℝ) / m))]
  norm_num

end RiemannSums

/-- Uniform distribution mod one implies convergence of the averages for monotone test
functions. -/
