/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Set Topology
open scoped ComplexInnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Aux


theorem exists_hasGenerator_add (hU : IsUnitaryGroup U) (x : H) :
    ∃ w : H, HasGenerator U w (Complex.I • (x - w)) := by
  set g : ℝ → H := fun u => Real.exp (-u) • U u x with hg
  have hc : Continuous g := ((Real.continuous_exp.comp continuous_neg).smul (hU.cont x))
  have hint : ∀ s : ℝ, IntegrableOn g (Ioi s) volume := by
    intro s
    refine Integrable.mono' (((exp_neg_integrableOn_Ioi s one_pos).mul_const ‖x‖))
      hc.aestronglyMeasurable.restrict ?_
    filter_upwards with u
    rw [hg, norm_smul]
    simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  set F : ℝ → H := fun s => ∫ u in Ioi s, g u with hF
  have hFU : ∀ s : ℝ, U s (F 0) = Real.exp s • F s := by
    intro s
    have h1 : U s (F 0) = ∫ u in Ioi (0:ℝ), U s (g u) :=
      ((U s).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hint 0)).symm
    have h2 : ∀ u : ℝ, U s (g u) = Real.exp s • g (s + u) := by
      intro u
      rw [hg]
      simp only [map_real_smul (U s) (U s).continuous, smul_smul]
      rw [← hU.add s u]
      congr 1
      rw [← Real.exp_add]
      ring_nf
    have h3 : ∫ u in Ioi (0:ℝ), g (s + u) = ∫ v in Ioi s, g v := by
      have := (measurePreserving_add_left (volume : Measure ℝ) s).setIntegral_preimage_emb
        (measurableEmbedding_addLeft s) g (Ioi s)
      simpa [Set.preimage, add_comm] using this
    rw [h1]
    simp only [h2]
    rw [integral_smul, h3]
  have hFsplit : ∀ s : ℝ, s ≤ 1 → F s = (∫ u in s..(1:ℝ), g u) + ∫ u in Ioi (1:ℝ), g u := by
    intro s hs
    have hsplit : Ioi s = Ioc s 1 ∪ Ioi 1 := by rw [Ioc_union_Ioi_eq_Ioi hs]
    rw [hF]
    simp only
    rw [hsplit, setIntegral_union (by simp [Set.disjoint_left])
      measurableSet_Ioi ((hint s).mono_set (fun a ha => ha.1)) (hint 1),
      intervalIntegral.integral_of_le hs]
  have hg0 : g 0 = x := by rw [hg]; simp [hU.zero]
  have hderiv : HasDerivAt F (-x) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (∫ u in s..(1:ℝ), g u) + ∫ u in Ioi (1:ℝ), g u) (-g 0) 0 :=
      (intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).add_const _
    rw [hg0] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)] with s hs
    exact hFsplit s (le_of_lt hs)
  refine ⟨F 0, ?_⟩
  have hlim1 : Tendsto (fun s : ℝ => (Real.exp s - 1) / s) (𝓝[≠] (0:ℝ)) (𝓝 1) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_exp 0)
    rw [Real.exp_zero] at h
    refine h.congr fun s => ?_
    simp [slope_def_field, div_eq_inv_mul]
  have hlim2 : Tendsto F (𝓝[≠] (0:ℝ)) (𝓝 (F 0)) :=
    hderiv.continuousAt.continuousWithinAt.tendsto
  have hlim3 : Tendsto (fun s : ℝ => s⁻¹ • (F s - F 0)) (𝓝[≠] (0:ℝ)) (𝓝 (-x)) := by
    refine (hasDerivAt_iff_tendsto_slope.mp hderiv).congr fun s => ?_
    simp [slope, vsub_eq_sub]
  have hmain : Tendsto (fun s : ℝ => ((Real.exp s - 1)/s) • F s + s⁻¹ • (F s - F 0))
      (𝓝[≠] (0:ℝ)) (𝓝 ((1:ℝ) • F 0 + -x)) := (hlim1.smul hlim2).add hlim3
  have hval : Complex.I • (Complex.I • (x - F 0)) = (1:ℝ) • F 0 + -x := by
    rw [smul_smul, Complex.I_mul_I]
    simp
    module
  rw [HasGenerator, hval]
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s _
  rw [hFU s, div_eq_mul_inv, mul_comm, ← smul_smul, ← smul_add]
  congr 1
  module

/-- The mirrored resolvent: for every `x` there is a `w` in the domain with `A w = i • (w - x)`,
i.e. `(A - i) w = -i • x`. -/
