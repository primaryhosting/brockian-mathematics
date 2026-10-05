/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate

namespace QPhys

section Strong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- On a finite-dimensional space, strong continuity of a family of operators implies
continuity in the operator norm. -/

theorem exists_generator_of_continuous (U : ℝ → A)
    (hgroup : ∀ s t, U (s + t) = U s * U t) (hone : U 0 = 1) (hcont : Continuous U) :
    ∃ B : A, ∀ t, HasDerivAt U (U t * B) t := by
  have hint : ∀ a b : ℝ, IntervalIntegrable U MeasureTheory.volume a b := fun a b =>
    hcont.intervalIntegrable a b
  set V : ℝ → A := fun r => ∫ t in (0:ℝ)..r, U t with hVdef
  have hV' : ∀ r, HasDerivAt V (U r) r := fun r =>
    intervalIntegral.integral_hasDerivAt_right (hint 0 r)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  -- pick `s > 0` on which `U` stays close to the identity
  obtain ⟨s, hs0, hsle⟩ : ∃ s : ℝ, 0 < s ∧ ∀ t ∈ Set.uIoc (0:ℝ) s, ‖U t - 1‖ ≤ 1/2 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := 0)) (1/2)
      (by norm_num)
    refine ⟨δ/2, by linarith, ?_⟩
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      linarith [ht.2]
    have := (h hdist).le
    simpa [hone, dist_eq_norm] using this
  have hne : s ≠ 0 := ne_of_gt hs0
  have hVs : ‖V s - s • (1 : A)‖ ≤ (1/2) * s := by
    have hsub : V s - s • (1 : A) = ∫ t in (0:ℝ)..s, (U t - 1) := by
      rw [intervalIntegral.integral_sub (hint 0 s) intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp [hVdef]
    rw [hsub]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 1/2) (f := fun t => U t - 1) (a := 0) (b := s) hsle
    simpa [abs_of_pos hs0] using this
  have h1a : ‖(1 : A) - s⁻¹ • V s‖ < 1 := by
    have heq : (1 : A) - s⁻¹ • V s = s⁻¹ • (s • (1 : A) - V s) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [heq, norm_smul]
    have hnorm : ‖s • (1 : A) - V s‖ ≤ 1/2 * s := by
      rw [← norm_neg]
      simpa [neg_sub] using hVs
    have hpos : ‖(s⁻¹ : ℝ)‖ = s⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs0)]
    rw [hpos]
    calc s⁻¹ * ‖s • (1 : A) - V s‖ ≤ s⁻¹ * (1/2 * s) :=
          mul_le_mul_of_nonneg_left hnorm (le_of_lt (inv_pos.2 hs0))
      _ = 1/2 := by field_simp
      _ < 1 := by norm_num
  set u : Aˣ := Units.oneSub ((1 : A) - s⁻¹ • V s) h1a with hudef
  have hu : (u : A) = s⁻¹ • V s := by simp [hudef, Units.oneSub]
  set W : A := s⁻¹ • ((u⁻¹ : Aˣ) : A) with hWdef
  have hVsa : V s = s • (s⁻¹ • V s) := by rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hVW : V s * W = 1 := by
    rw [hVsa, hWdef, smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hne, one_smul,
      ← hu, u.mul_inv]
  have hkey : ∀ r, U r * V s = V (r + s) - V r := by
    intro r
    have h1 : U r * V s = ∫ t in (0:ℝ)..s, U r * U t :=
      ((ContinuousLinearMap.mul ℝ A (U r)).intervalIntegral_comp_comm (hint 0 s)).symm
    have h2 : (∫ t in (0:ℝ)..s, U r * U t) = ∫ t in (0:ℝ)..s, U (r + t) := by
      simp only [hgroup]
    have h3 : (∫ t in (0:ℝ)..s, U (r + t)) = ∫ t in (r + 0)..(r + s), U t :=
      intervalIntegral.integral_comp_add_left U r
    have h4 : V (r + s) - V r = ∫ t in r..(r + s), U t :=
      intervalIntegral.integral_interval_sub_left (hint 0 (r + s)) (hint 0 r)
    rw [h1, h2, h3, h4, add_zero]
  refine ⟨(U s - 1) * W, ?_⟩
  intro r
  have hUeq : ∀ r, U r = (V (r + s) - V r) * W := by
    intro r
    rw [← hkey r, mul_assoc, hVW, mul_one]
  have hd : HasDerivAt (fun r => (V (r + s) - V r) * W) ((U (r + s) - U r) * W) r :=
    ((HasDerivAt.comp_add_const r s (hV' (r + s))).sub (hV' r)).mul_const W
  have hd2 : HasDerivAt U ((U (r + s) - U r) * W) r :=
    hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hUeq)
  have hval : (U (r + s) - U r) * W = U r * ((U s - 1) * W) := by
    rw [hgroup r s]
    noncomm_ring
  rwa [hval] at hd2

/-- The generator commutes with the group: `U t * B = B * U t`. -/
