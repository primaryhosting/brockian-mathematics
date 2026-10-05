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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Finset MeasureTheory
open scoped Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` with values in `[0, 1)` is *uniformly distributed* if for every
`c ∈ [0, 1]` the proportion of the first `N` terms lying in `[0, c)` tends to `c`. -/

theorem equidistribution_of_BV_uniform {x : ℕ → ℝ} (hx : UniformlyDistributed x)
    {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f (x n)) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  set P : ℝ → ℝ := fun t => p (clamp t) with hPdef
  set Q : ℝ → ℝ := fun t => q (clamp t) with hQdef
  have hP : Monotone P := monotone_comp_clamp hp
  have hQ : Monotone Q := monotone_comp_clamp hq
  have hfeq : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = P t - Q t := by
    intro t ht
    have : f t = p t - q t := by rw [hpq]; rfl
    rw [this, hPdef, hQdef]
    simp only [clamp_eq_self ht]
  have hfx : ∀ n, f (x n) = P (x n) - Q (x n) := fun n =>
    hfeq (x n) ⟨(hx.1 n).1, (hx.1 n).2.le⟩
  have hint : (∫ t in (0 : ℝ)..1, f t)
      = (∫ t in (0 : ℝ)..1, P t) - ∫ t in (0 : ℝ)..1, Q t := by
    rw [← intervalIntegral.integral_sub (hP.intervalIntegrable) (hQ.intervalIntegrable)]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (zero_le_one' ℝ)] at ht
    exact hfeq t ht
  have hPlim := tendsto_average_of_monotone hx hP
  have hQlim := tendsto_average_of_monotone hx hQ
  rw [hint]
  refine (hPlim.sub hQlim).congr ?_
  intro N
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp only [hfx]

/-- The identity has bounded variation on `[0, 1]`. -/
