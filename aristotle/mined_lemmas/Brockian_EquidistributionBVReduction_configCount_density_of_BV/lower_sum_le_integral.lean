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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory
open scoped BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `S`:
the count of "configurations" of the first `N` terms of the sequence inside the window `S`. -/

lemma lower_sum_le_integral (hg : MonotoneOn g (Icc (0 : ℝ) 1)) (hk : 0 < k) :
    ∑ i ∈ Finset.range k, g ((i : ℝ) / k) / k ≤ ∫ t in (0 : ℝ)..1, g t := by
  rw [← sum_integral_nodes hg hk]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik := Finset.mem_range.1 hi
  have hml : ((i : ℝ) / k) ∈ Icc (0 : ℝ) 1 :=
    Icc_node_subset hk hik ⟨le_refl _, node_le hk i⟩
  have hmono : ∀ t ∈ Icc ((i : ℝ) / k) (((i : ℝ) + 1) / k), g ((i : ℝ) / k) ≤ g t := fun t ht =>
    hg hml (Icc_node_subset hk hik ht) ht.1
  have hcalc := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => g ((i : ℝ) / k))
    (g := g) (node_le hk i) intervalIntegrable_const (intervalIntegrable_node hg hk hik) hmono
  rw [intervalIntegral.integral_const] at hcalc
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hw : (((i : ℝ) + 1) / k - (i : ℝ) / k) = 1 / k := by field_simp; ring
  rw [hw] at hcalc
  simpa [smul_eq_mul, one_div, div_eq_inv_mul] using hcalc

