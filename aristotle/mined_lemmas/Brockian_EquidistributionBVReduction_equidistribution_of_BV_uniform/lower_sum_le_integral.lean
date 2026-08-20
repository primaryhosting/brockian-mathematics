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

open Filter Finset MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

lemma lower_sum_le_integral (hg : Monotone g) {K : ℕ} (hK : 0 < K) :
    ∑ i ∈ Finset.range K, g ((i : ℝ) / K) / K ≤ ∫ t in (0:ℝ)..1, g t := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hsum : ∑ i ∈ Finset.range K, ∫ t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g t =
      ∫ t in (0:ℝ)..1, g t := by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun i : ℕ => (i : ℝ) / K) (f := g) (μ := volume) (n := K)
      (fun k _ => hg.intervalIntegrable)
    simpa [Nat.cast_add, Nat.cast_one, div_self (ne_of_gt hKpos)] using this
  rw [← hsum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hle : (i : ℝ) / K ≤ ((i : ℝ) + 1) / K := by
    rw [div_le_div_iff_of_pos_right hKpos]; linarith
  have hmono : ∫ t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g ((i : ℝ) / K) ≤
      ∫ t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g t :=
    intervalIntegral.integral_mono_on hle intervalIntegrable_const
      hg.intervalIntegrable (fun t ht => hg ht.1)
  calc g ((i : ℝ) / K) / K
      = ∫ _t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g ((i : ℝ) / K) := by
        rw [intervalIntegral.integral_const, smul_eq_mul,
          show ((i : ℝ) + 1) / K - (i : ℝ) / K = 1 / K by rw [div_sub_div_same]; norm_num]
        ring
    _ ≤ _ := hmono

/-- The upper Riemann sum of a monotone function overestimates its integral. -/
