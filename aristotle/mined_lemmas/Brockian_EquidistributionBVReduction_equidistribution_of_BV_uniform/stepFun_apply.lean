import Brockian.EquidistributionBVReduction

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

import Mathlib
/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The empirical frequency with which the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/

lemma stepFun_apply (hk : 0 < k) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    stepFun k c t = c ⌊(k : ℝ) * t⌋₊ := by
  classical
  set i0 := ⌊(k : ℝ) * t⌋₊ with hi0
  have hmem : i0 ∈ Finset.range k := Finset.mem_range.2 (floor_lt_of_mem hk ht)
  rw [stepFun, Finset.sum_eq_single_of_mem i0 hmem]
  · rw [Set.indicator_of_mem]
    exact (mem_Ico_div_iff hk ht.1 i0).2 rfl
  · intro j _ hj
    rw [Set.indicator_of_notMem]
    intro hcon
    exact hj ((mem_Ico_div_iff hk ht.1 j).1 hcon).symm

