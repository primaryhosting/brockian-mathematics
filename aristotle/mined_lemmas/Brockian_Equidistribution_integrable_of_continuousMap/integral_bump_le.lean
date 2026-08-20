import Brockian.Equidistribution

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
# Weyl equidistribution

This file develops, from scratch, Weyl's criterion for equidistribution modulo one and applies
it to the sequence `n ↦ n * α` for irrational `α`.

The main statement is `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`, which
is *conditional* on the asymptotic vanishing of the Weyl exponential sums, and its unconditional
consequence `Brockian.Equidistribution.equidistributedMod1_natMul_irrational`.
-/

namespace Brockian.Equidistribution

open MeasureTheory Filter Finset Complex Topology Metric

open scoped Real

noncomputable section

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem integral_bump_le (c s ep : ℝ) (hep : 0 < ep) (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) :
    (∫ z, bump c s ep z) ≤ 2 * s := by
  rw [integral_bump_eq]
  set ψ : ℝ → ℝ := fun t => min 1 (max 0 ((s - |t - c|) / ep)) with hψ
  have hcont : Continuous ψ := by fun_prop
  have hii : ∀ u v : ℝ, IntervalIntegrable ψ volume u v := fun u v => hcont.intervalIntegrable u v
  have hzero : ∀ t : ℝ, s ≤ |t - c| → ψ t = 0 := by
    intro t ht
    have : (s - |t - c|) / ep ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hep.le
    simp [hψ, max_eq_left this]
  have h1 : (∫ t in (c - 1 / 2)..(c - s), ψ t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact hzero t (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2])
  have h3 : (∫ t in (c + s)..(c + 1 / 2), ψ t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact hzero t (by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.1])
  have h2 : (∫ t in (c - s)..(c + s), ψ t) ≤ 2 * s := by
    have := intervalIntegral.integral_mono_on (f := ψ) (g := fun _ => (1 : ℝ)) (a := c - s)
      (b := c + s) (by linarith) (hii _ _) (by simp [intervalIntegrable_const])
      (fun t _ => min_le_left _ _)
    simpa [mul_comm] using this.trans_eq (by simp; ring)
  have hsplit : (∫ t in (c - 1 / 2)..(c - s), ψ t) + (∫ t in (c - s)..(c + s), ψ t)
      + (∫ t in (c + s)..(c + 1 / 2), ψ t) = ∫ t in (c - 1 / 2)..(c + 1 / 2), ψ t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
  rw [← hsplit, h1, h3]
  linarith

