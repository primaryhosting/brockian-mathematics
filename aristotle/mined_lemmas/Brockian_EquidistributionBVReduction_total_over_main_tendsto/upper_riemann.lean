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

/-
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Filter Topology
open scoped BigOperators Classical

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `[a, b)`. -/

lemma upper_riemann (hg : Monotone g) (hm : 0 < m) :
    (∫ t in (0:ℝ)..1, g t) ≤ ∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) * (1 / m) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have key := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i:ℝ)/m) (n := m) (f := g) (μ := MeasureTheory.volume)
    (fun k _ => hg.intervalIntegrable)
  simp only [Nat.cast_zero, zero_div, div_self (ne_of_gt hm')] at key
  push_cast at key
  rw [← key]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle : (i:ℝ)/m ≤ ((i : ℝ) + 1)/m := by gcongr; linarith
  have heq : g (((i:ℝ)+1)/m) * (1/m) = ∫ _u in ((i:ℝ)/m)..((i:ℝ)+1)/m, g (((i:ℝ)+1)/m) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  rw [heq]
  exact intervalIntegral.integral_mono_on hle hg.intervalIntegrable intervalIntegrable_const
    (fun u hu => hg hu.2)

