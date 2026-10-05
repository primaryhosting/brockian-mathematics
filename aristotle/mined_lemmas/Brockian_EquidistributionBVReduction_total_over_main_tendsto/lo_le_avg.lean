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

lemma lo_le_avg (hg : Monotone g) (hm : 0 < m) (N : ℕ) :
    ∑ i ∈ Finset.range m,
        g ((i : ℝ) / m) * ((countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) / N)
      ≤ total g x N / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [total, countIco]
  · have hN' : (0:ℝ) < N := by exact_mod_cast hN
    have hrw : ∑ i ∈ Finset.range m,
        g ((i : ℝ) / m) * ((countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) / N)
        = (∑ i ∈ Finset.range m,
            g ((i : ℝ) / m) * (countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_div_assoc]
    rw [hrw]
    gcongr
    exact sum_le_total hg hm

