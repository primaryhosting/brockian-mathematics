import Mathlib
import RequestProject.Brockian.EquidistributionBVReduction

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

open Filter Finset Set
open scoped Topology BigOperators Classical

set_option maxHeartbeats 1000000

namespace Brockian
namespace EquidistributionBVReduction

/-- `countIn x a b N` is the number of indices `n < N` with `x n ∈ [a, b)`. -/

lemma integral_le_upper (hg : MonotoneOn g (Set.Icc 0 1)) (hk : 0 < k) :
    (∫ t in (0 : ℝ)..1, g t) ≤ ∑ j ∈ Finset.range k, g (((j : ℝ) + 1) / k) * (1 / (k : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set a : ℕ → ℝ := fun j => (j : ℝ) / k with ha
  have hmemIcc : ∀ j ≤ k, a j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    show (j : ℝ) / k ≤ 1
    rw [div_le_one hk']
    exact_mod_cast hj
  have hle : ∀ j, a j ≤ a (j + 1) := by
    intro j
    show (j : ℝ) / k ≤ ((j + 1 : ℕ) : ℝ) / k
    gcongr
    linarith
  have hsub : ∀ j < k, Set.Icc (a j) (a (j + 1)) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro j hj t ht
    exact ⟨le_trans (hmemIcc j hj.le).1 ht.1, le_trans ht.2 (hmemIcc (j + 1) hj).2⟩
  have hint : ∀ j < k, IntervalIntegrable g MeasureTheory.volume (a j) (a (j + 1)) := by
    intro j hj
    apply MonotoneOn.intervalIntegrable
    apply hg.mono
    rw [Set.uIcc_of_le (hle j)]
    exact hsub j hj
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals hint
  have h0 : a 0 = 0 := by show ((0 : ℕ) : ℝ) / k = 0; simp
  have h1 : a k = 1 := by show (k : ℝ) / k = 1; field_simp
  rw [h0, h1] at hsplit
  rw [← hsplit]
  refine Finset.sum_le_sum ?_
  intro j hj
  have hj' : j < k := Finset.mem_range.1 hj
  have hmono : ∀ t ∈ Set.Icc (a j) (a (j + 1)), g t ≤ g (a (j + 1)) := fun t ht =>
    hg (hsub j hj' ht) (hmemIcc (j + 1) hj') ht.2
  have key := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (hle j) (hint j hj')
    intervalIntegrable_const hmono
  rw [intervalIntegral.integral_const] at key
  have hdiff : a (j + 1) - a j = 1 / (k : ℝ) := by
    show ((j + 1 : ℕ) : ℝ) / k - (j : ℝ) / k = 1 / k
    push_cast; ring
  have hcast : a (j + 1) = ((j : ℝ) + 1) / k := by
    show ((j + 1 : ℕ) : ℝ) / k = _
    push_cast; ring
  rw [hdiff, smul_eq_mul, hcast] at key
  rw [hcast]
  linarith

/-- The integral is bounded below by the lower Darboux sum. -/
