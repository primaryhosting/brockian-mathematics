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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem integrable_uncurry_path (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    Integrable (Function.uncurry fun (t s : ℝ) =>
        (ρ * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
  classical
  obtain ⟨mr, hmr0, hmr⟩ := exists_pos_sub_posSemidef hρ
  obtain ⟨ms, hms0, hms⟩ := exists_pos_sub_posSemidef hσ
  set m : ℝ := min mr ms with hm
  have hm0 : 0 < m := lt_min hmr0 hms0
  have hmono : ∀ {A : Mat n} {m₀ : ℝ}, (A - ((m₀ : ℝ) : ℂ) • 1).PosSemidef → m ≤ m₀ →
      (A - ((m : ℝ) : ℂ) • 1).PosSemidef := by
    intro A m₀ hA hle
    have hid : A - ((m : ℝ) : ℂ) • 1
        = (A - ((m₀ : ℝ) : ℂ) • 1) + ((m₀ - m : ℝ) : ℂ) • (1 : Mat n) := by
      push_cast
      module
    rw [hid]
    refine hA.add (Matrix.PosSemidef.smul Matrix.PosSemidef.one ?_)
    have : (0:ℝ) ≤ m₀ - m := by linarith
    exact_mod_cast this
  have hρm : (ρ - ((m : ℝ) : ℂ) • 1).PosSemidef := hmono hmr (min_le_left _ _)
  have hσm : (σ - ((m : ℝ) : ℂ) • 1).PosSemidef := hmono hms (min_le_right _ _)
  have hpathm : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (pathState ρ σ s - ((m : ℝ) : ℂ) • 1).PosSemidef := by
    intro s h0 h1
    have hid : pathState ρ σ s - ((m : ℝ) : ℂ) • 1
        = ((1 - s : ℝ) : ℂ) • (σ - ((m : ℝ) : ℂ) • 1)
          + ((s : ℝ) : ℂ) • (ρ - ((m : ℝ) : ℂ) • 1) := by
      rw [pathState_eq]
      push_cast
      module
    rw [hid]
    refine (Matrix.PosSemidef.smul hσm ?_).add (Matrix.PosSemidef.smul hρm ?_)
    · have : (0:ℝ) ≤ 1 - s := by linarith
      exact_mod_cast this
    · exact_mod_cast h0
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1)) := ⟨by simp⟩
  set K : ℝ := (frobSq ρ + frobSq (ρ - σ)) / 2 with hK
  rw [MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.Integrable.mono'
    (g := fun p : ℝ × ℝ => K * ((m + p.1)⁻¹ * (m + p.1)⁻¹)) ?_ ?_ ?_
  · rw [← MeasureTheory.Measure.prod_restrict]
    exact ((integrableOn_resSq hm0).const_mul K).comp_fst _
  · refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    exact (continuousAt_path_trace hρ hσ ρ (ρ - σ) (le_of_lt hp.1) (le_of_lt hp.2.1)
      (le_of_lt hp.2.2)).continuousWithinAt
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have ht : (0:ℝ) ≤ p.1 := le_of_lt hp1
    have hs0 : (0:ℝ) ≤ p.2 := le_of_lt hp2.1
    have hs1 : p.2 ≤ 1 := le_of_lt hp2.2
    have hωp : (pathState ρ σ p.2).PosDef := pathState_posDef hρ hσ hs0 hs1
    have hmt : 0 < m + p.1 := by linarith
    have hbound := abs_trace_res_quad_le hωp
      (fun i => eigV_ge_of_sub_posSemidef hωp (hpathm p.2 hs0 hs1) i) ht hmt ρ (ρ - σ)
    simpa [Function.uncurry, Real.norm_eq_abs, hK] using hbound

/-- **The integral representation of the relative entropy.** -/
