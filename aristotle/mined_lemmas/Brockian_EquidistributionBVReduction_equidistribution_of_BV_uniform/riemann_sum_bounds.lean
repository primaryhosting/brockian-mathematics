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

lemma riemann_sum_bounds (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc (0 : ℝ) 1)) {k : ℕ}
    (hk : 0 < k) :
    (∑ i ∈ Finset.range k, f ((i : ℝ) / k) / k) ≤ (∫ t in (0 : ℝ)..1, f t) ∧
      (∫ t in (0 : ℝ)..1, f t) ≤ ∑ i ∈ Finset.range k, f (((i : ℝ) + 1) / k) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set a : ℕ → ℝ := fun i => (i : ℝ) / k with ha
  have hstep : ∀ i : ℕ, a (i + 1) - a i = 1 / k := by
    intro i
    simp only [ha]
    push_cast
    field_simp
    ring
  have hle : ∀ i : ℕ, a i ≤ a (i + 1) := by
    intro i
    have := hstep i
    have : (0 : ℝ) < 1 / k := by positivity
    linarith [hstep i]
  have hsubset : ∀ i, i < k → Set.Icc (a i) (a (i + 1)) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro i hi
    apply Set.Icc_subset_Icc
    · simp only [ha]; positivity
    · simp only [ha]
      rw [div_le_one hk']
      have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
      push_cast
      linarith
  have hmono' : ∀ i, i < k → MonotoneOn f (Set.uIcc (a i) (a (i + 1))) := by
    intro i hi
    rw [Set.uIcc_of_le (hle i)]
    exact hf.mono (hsubset i hi)
  have hint : ∀ i < k, IntervalIntegrable f volume (a i) (a (i + 1)) := fun i hi =>
    (hmono' i hi).intervalIntegrable
  have hsplit : ∑ i ∈ Finset.range k, ∫ t in (a i)..(a (i + 1)), f t
      = ∫ t in (a 0)..(a k), f t := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [ha]
  have hak : a k = 1 := by
    simp only [ha]
    field_simp
  rw [ha0, hak] at hsplit
  constructor
  · rw [← hsplit]
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : i < k := Finset.mem_range.1 hi
    have hlow : ∀ t ∈ Set.Icc (a i) (a (i + 1)), f (a i) ≤ f t := by
      intro t ht
      exact hf (hsubset i hik (Set.mem_Icc.2 ⟨le_rfl, hle i⟩)) (hsubset i hik ht) ht.1
    have := intervalIntegral.integral_mono_on (μ := volume) (hle i)
      (intervalIntegrable_const (c := f (a i))) (hint i hik) hlow
    rw [intervalIntegral.integral_const, hstep i] at this
    simpa [ha, smul_eq_mul, div_eq_inv_mul] using this
  · rw [← hsplit]
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : i < k := Finset.mem_range.1 hi
    have hhigh : ∀ t ∈ Set.Icc (a i) (a (i + 1)), f t ≤ f (a (i + 1)) := by
      intro t ht
      exact hf (hsubset i hik ht) (hsubset i hik (Set.mem_Icc.2 ⟨hle i, le_rfl⟩)) ht.2
    have := intervalIntegral.integral_mono_on (μ := volume) (hle i) (hint i hik)
      (intervalIntegrable_const (c := f (a (i + 1)))) hhigh
    rw [intervalIntegral.integral_const, hstep i] at this
    have hcast : a (i + 1) = ((i : ℝ) + 1) / k := by simp only [ha]; push_cast; ring
    rw [hcast] at this ⊢
    simpa [smul_eq_mul, div_eq_inv_mul] using this

