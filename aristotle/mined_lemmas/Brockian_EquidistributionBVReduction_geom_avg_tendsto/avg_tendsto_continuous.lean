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
# Equidistribution of irrational rotations and the bounded-variation reduction

This file develops, from scratch, Weyl's equidistribution theorem for the sequence
`n ↦ n • α mod 1` (`α` irrational) and reduces averages of functions of bounded variation
to their integral.

The final result `total_over_main_tendsto` states that, for a function `f` of bounded
variation on `[0,1]` with nonzero integral, the *total*
`∑_{n < N} f (fract (n α))` divided by the *main term* `N * ∫₀¹ f` tends to `1`.
-/

open Filter Finset Set MeasureTheory Metric
open scoped Topology

namespace Brockian.EquidistributionBVReduction

noncomputable section

/-- A sequence of reals is equidistributed mod one when, for every subinterval `[a,b) ⊆ [0,1]`,
the proportion of the first `N` fractional parts lying in `[a, b)` tends to `b - a`. -/

theorem avg_tendsto_continuous {α : ℝ} (hα : Irrational α) (F : C(AddCircle (1:ℝ), ℂ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)) atTop
      (𝓝 (∫ t : AddCircle (1:ℝ), F t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmem : F ∈ closure
      ((Submodule.span ℂ (Set.range (fourier (T := (1:ℝ))))) : Set C(AddCircle (1:ℝ), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]; trivial
  obtain ⟨G, hGmem, hFG⟩ := Metric.mem_closure_iff.1 hmem (ε/4) (by positivity)
  rw [dist_eq_norm] at hFG
  obtain ⟨N₁, hN₁⟩ :=
    Metric.tendsto_atTop.1 (avg_tendsto_of_mem_span hα G hGmem) (ε/4) (by positivity)
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have hdiff : ‖(∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)
      - (∑ n ∈ range N, G ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)‖ ≤ ‖F - G‖ := by
    rw [div_sub_div_same, ← sum_sub_distrib, norm_div, Complex.norm_natCast, div_le_iff₀ hNpos]
    calc ‖∑ n ∈ range N, (F ((n * α : ℝ) : AddCircle (1:ℝ)) - G ((n * α : ℝ) : AddCircle (1:ℝ)))‖
        ≤ ∑ n ∈ range N,
            ‖F ((n * α : ℝ) : AddCircle (1:ℝ)) - G ((n * α : ℝ) : AddCircle (1:ℝ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ range N, ‖F - G‖ := by
          refine sum_le_sum fun n _ => ?_
          simpa using (F - G).norm_coe_le_norm ((n * α : ℝ) : AddCircle (1:ℝ))
      _ = ‖F - G‖ * N := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hint : ‖(∫ t : AddCircle (1:ℝ), G t) - ∫ t : AddCircle (1:ℝ), F t‖ ≤ ‖F - G‖ := by
    have hsub : (∫ t : AddCircle (1:ℝ), G t) - ∫ t : AddCircle (1:ℝ), F t
        = ∫ t : AddCircle (1:ℝ), (G - F) t := by
      simp only [ContinuousMap.sub_apply]
      rw [integral_sub (integrable_of_continuousMap G) (integrable_of_continuousMap F)]
    rw [hsub]
    calc ‖∫ t : AddCircle (1:ℝ), (G - F) t‖ ≤ ‖G - F‖ := norm_integral_le_norm _
      _ = ‖F - G‖ := norm_sub_rev _ _
  have h3 := hN₁ N (le_trans (le_max_left _ _) hN)
  rw [dist_eq_norm] at h3 ⊢
  calc ‖(∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ) - ∫ t : AddCircle (1:ℝ), F t‖
      ≤ ‖(∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)
          - (∑ n ∈ range N, G ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)‖
        + ‖(∑ n ∈ range N, G ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)
            - ∫ t : AddCircle (1:ℝ), G t‖
        + ‖(∫ t : AddCircle (1:ℝ), G t) - ∫ t : AddCircle (1:ℝ), F t‖ := by
        have := norm_add₃_le (a := (∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)
          - (∑ n ∈ range N, G ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ))
          (b := (∑ n ∈ range N, G ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)
            - ∫ t : AddCircle (1:ℝ), G t)
          (c := (∫ t : AddCircle (1:ℝ), G t) - ∫ t : AddCircle (1:ℝ), F t)
        simpa using this
    _ < ε := by linarith [hdiff, hint, h3]

/-- **Weyl's theorem, real continuous form.** -/
