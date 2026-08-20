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

theorem cavg_tendsto_integral (x : ℕ → ℝ) (hx : WeylCondition x) (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (cavg x f) atTop (𝓝 (∫ z, f z)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hdense : f ∈
      closure ((Submodule.span ℂ (Set.range (@fourier 1))) : Set C(AddCircle (1 : ℝ), ℂ)) := by
    have : f ∈ (Submodule.span ℂ (Set.range (@fourier 1))).topologicalClosure := by
      rw [span_fourier_closure_eq_top]; trivial
    exact this
  obtain ⟨p, hp_mem, hp⟩ := Metric.mem_closure_iff.1 hdense (δ / 4) (by linarith)
  have hnorm : ‖f - p‖ < δ / 4 := by rwa [dist_eq_norm] at hp
  have h1 := cavg_tendsto_of_mem_span x hx hp_mem
  rw [Metric.tendsto_atTop] at h1
  obtain ⟨M, hM⟩ := h1 (δ / 4) (by linarith)
  refine ⟨M, fun N hN => ?_⟩
  have e1 : dist (cavg x f N) (cavg x p N) ≤ δ / 4 := by
    rw [dist_eq_norm]
    have := norm_cavg_le x (f - p) N
    rw [show ⇑(f - p) = (⇑f - ⇑p) from rfl, cavg_sub] at this
    linarith
  have e2 : dist (∫ z, p z) (∫ z, f z) ≤ δ / 4 := by
    rw [dist_eq_norm, norm_sub_rev]
    have := norm_integral_le_norm (f - p)
    rw [show (∫ z, (f - p) z) = (∫ z, f z) - ∫ z, p z from by
      simp only [ContinuousMap.sub_apply]
      exact integral_sub (integrable_of_continuousMap f) (integrable_of_continuousMap p)] at this
    linarith
  have e3 : dist (cavg x p N) (∫ z, p z) < δ / 4 := hM N hN
  calc dist (cavg x f N) (∫ z, f z)
      ≤ dist (cavg x f N) (cavg x p N) + dist (cavg x p N) (∫ z, p z)
        + dist (∫ z, p z) (∫ z, f z) := dist_triangle4 _ _ _ _
    _ < δ := by linarith

