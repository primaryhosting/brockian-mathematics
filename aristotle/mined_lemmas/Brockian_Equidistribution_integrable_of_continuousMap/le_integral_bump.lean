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

theorem le_integral_bump (c s ep : ℝ) (hep : 0 < ep) (hs' : s ≤ 1 / 2) :
    2 * (s - ep) ≤ ∫ z, bump c s ep z := by
  rw [integral_bump_eq]
  set ψ : ℝ → ℝ := fun t => min 1 (max 0 ((s - |t - c|) / ep)) with hψ
  have hcont : Continuous ψ := by fun_prop
  have hii : ∀ u v : ℝ, IntervalIntegrable ψ volume u v := fun u v => hcont.intervalIntegrable u v
  have hnonneg : ∀ t, 0 ≤ ψ t := fun t => le_min zero_le_one (le_max_left _ _)
  rcases lt_or_ge (s - ep) 0 with hneg | hpos
  · have : (0 : ℝ) ≤ ∫ t in (c - 1 / 2)..(c + 1 / 2), ψ t :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ => hnonneg t
    linarith
  · set u := s - ep with hu
    have hu2 : u ≤ 1 / 2 := by linarith
    have hone : ∀ t : ℝ, |t - c| ≤ u → ψ t = 1 := by
      intro t ht
      have h1 : 1 ≤ (s - |t - c|) / ep := by rw [le_div_iff₀ hep]; linarith
      simp [hψ, max_eq_right (by linarith : (0 : ℝ) ≤ (s - |t - c|) / ep), min_eq_left h1]
    have h2 : (∫ t in (c - u)..(c + u), ψ t) = 2 * u := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
      · simp; ring
      · intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact hone t (by rw [abs_le]; constructor <;> [linarith [ht.1]; linarith [ht.2]])
    have h1 : (0 : ℝ) ≤ ∫ t in (c - 1 / 2)..(c - u), ψ t :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ => hnonneg t
    have h3 : (0 : ℝ) ≤ ∫ t in (c + u)..(c + 1 / 2), ψ t :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ => hnonneg t
    have hsplit : (∫ t in (c - 1 / 2)..(c - u), ψ t) + (∫ t in (c - u)..(c + u), ψ t)
        + (∫ t in (c + u)..(c + 1 / 2), ψ t) = ∫ t in (c - 1 / 2)..(c + 1 / 2), ψ t := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
        intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
    rw [← hsplit, h2]
    linarith

/-! ### From membership of arcs to fractional parts -/

