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

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- The frequency with which the fractional parts of the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/

lemma integral_le_upper_sum (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) {k : ℕ} (hk : 0 < k) :
    (∫ t in (0 : ℝ)..1, g t) ≤ ∑ j ∈ Finset.range k, g (((j : ℝ) + 1) / k) / k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  set a : ℕ → ℝ := fun j => (j : ℝ) / k with ha
  have hmem : ∀ j : ℕ, j ≤ k → a j ∈ Set.Icc (0:ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [ha]; dsimp only; rw [div_le_one hk0]; exact_mod_cast hj
  have hle : ∀ j : ℕ, a j ≤ a (j+1) := by
    intro j; rw [ha]; dsimp only; gcongr; linarith
  have hsub : ∀ j, j < k → Set.uIcc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 := by
    intro j hj
    rw [Set.uIcc_of_le (hle j)]
    exact Set.Icc_subset_Icc (hmem j hj.le).1 (hmem (j+1) hj).2
  have hint : ∀ j < k, IntervalIntegrable g MeasureTheory.volume (a j) (a (j+1)) :=
    fun j hj => (hg.mono (hsub j hj)).intervalIntegrable
  have hsum : ∑ j ∈ Finset.range k, ∫ t in (a j)..(a (j+1)), g t = ∫ t in (0:ℝ)..1, g t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hint]
    have h0 : a 0 = 0 := by simp [ha]
    have h1 : a k = 1 := by rw [ha]; field_simp
    rw [h0, h1]
  rw [← hsum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hjk := Finset.mem_range.mp hj
  have hdiff : a (j+1) - a j = 1/k := by rw [ha]; push_cast; field_simp; ring
  have hconst : ∫ _t in (a j)..(a (j+1)), g (a (j+1)) = g (a (j+1)) * (1/k) := by
    rw [intervalIntegral.integral_const, hdiff, smul_eq_mul]; ring
  have hmain := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (hle j)
    (hint j hjk) (intervalIntegrable_const (c := g (a (j+1))))
    (fun t ht => hg (hsub j hjk (by rw [Set.uIcc_of_le (hle j)]; exact ht))
      (hmem (j+1) hjk) ht.2)
  rw [hconst] at hmain
  calc (∫ t in (a j)..(a (j+1)), g t) ≤ g (a (j+1)) * (1/k) := hmain
    _ = g (((j:ℝ)+1)/k) / k := by rw [ha]; push_cast; ring

/-- Convergence of the weighted counting sums, from uniform distribution. -/
