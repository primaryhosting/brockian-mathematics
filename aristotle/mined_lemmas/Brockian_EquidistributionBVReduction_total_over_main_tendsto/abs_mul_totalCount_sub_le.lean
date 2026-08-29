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
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- The *total* count: the number of natural numbers `n < N` that lie in the
residue class `a` modulo `q`. -/

lemma abs_mul_totalCount_sub_le (q a N : ℕ) (hq : 0 < q) :
    |(q : ℝ) * (totalCount q a N : ℝ) - (N : ℝ)| ≤ (q : ℝ) := by
  obtain ⟨hA, hB⟩ := totalCount_bounds q a N hq
  have hA' : (N : ℝ) ≤ (q : ℝ) * (totalCount q a N : ℝ) + (q : ℝ) := by exact_mod_cast hA
  have hB' : (q : ℝ) * (totalCount q a N : ℝ) ≤ (N : ℝ) + (q : ℝ) := by exact_mod_cast hB
  rw [abs_le]
  constructor <;> linarith

/-- **Equidistribution in a residue class**: the total count over the main term tends to `1`.

This discharges the named hypothesis `total_over_main_tendsto`, making it unconditional. -/
