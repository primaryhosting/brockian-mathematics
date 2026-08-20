import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Math

/-- Algebraic identity: the positive root of `‖a + t v‖² = 1` (with `‖a‖ ≤ 1`, `v ≠ 0`)
is `t = (-⟪a,v⟫ + √(⟪a,v⟫² + ‖v‖²(1-‖a‖²)))/‖v‖²`. -/

theorem brouwer_complex (f : ℂ → ℂ) (hf : ContinuousOn f (Metric.closedBall 0 1))
    (hmaps : Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ z ∈ Metric.closedBall (0 : ℂ) 1, f z = z := by
  by_contra hcon
  push_neg at hcon
  -- radial projection onto the closed unit disk
  set a : ℂ → ℂ := fun z => (max 1 ‖z‖)⁻¹ • z with ha
  have hac : Continuous a := by
    refine Continuous.smul ((continuous_const.max continuous_norm).inv₀ ?_) continuous_id
    intro z
    have : (1 : ℝ) ≤ max 1 ‖z‖ := le_max_left _ _
    linarith
  have haball : ∀ z, a z ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z
    simp only [Metric.mem_closedBall, dist_zero_right, ha]
    rw [norm_smul]
    have h1 : (1 : ℝ) ≤ max 1 ‖z‖ := le_max_left _ _
    have h2 : ‖z‖ ≤ max 1 ‖z‖ := le_max_right _ _
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith), inv_mul_le_iff₀ (by linarith)]
    linarith
  have haid : ∀ z : ℂ, ‖z‖ ≤ 1 → a z = z := by
    intro z hz; simp [ha, max_eq_left hz]
  have hanorm : ∀ z, (a z).re ^ 2 + (a z).im ^ 2 ≤ 1 := by
    intro z
    have h := haball z
    simp only [Metric.mem_closedBall, dist_zero_right] at h
    have : Complex.normSq (a z) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (a z)]
    simpa [Complex.normSq_apply, sq] using this
  set b : ℂ → ℂ := fun z => f (a z)
  have hbc : Continuous b := hf.comp_continuous hac haball
  have hbnorm : ∀ z, (b z).re ^ 2 + (b z).im ^ 2 ≤ 1 := by
    intro z
    have h := hmaps (haball z)
    simp only [Metric.mem_closedBall, dist_zero_right] at h
    have : Complex.normSq (b z) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (b z)]
    simpa [Complex.normSq_apply, sq] using this
  set v : ℂ → ℂ := fun z => a z - b z with hv
  have hvc : Continuous v := hac.sub hbc
  have hvne : ∀ z, v z ≠ 0 := fun z h => hcon (a z) (haball z) (sub_eq_zero.mp h).symm
  set n : ℂ → ℝ := fun z => (v z).re ^ 2 + (v z).im ^ 2 with hn
  have hnpos : ∀ z, 0 < n z := by
    intro z
    have h : 0 < Complex.normSq (v z) := Complex.normSq_pos.mpr (hvne z)
    rw [Complex.normSq_apply] at h
    simp only [hn]
    nlinarith [h]
  have hnc : Continuous n := by fun_prop
  set d : ℂ → ℝ := fun z => (a z).re * (v z).re + (a z).im * (v z).im with hd
  have hdc : Continuous d := by fun_prop
  set disc : ℂ → ℝ :=
    fun z => d z ^ 2 + n z * (1 - ((a z).re ^ 2 + (a z).im ^ 2)) with hdisc
  have hdiscc : Continuous disc := by fun_prop
  have hdiscnn : ∀ z, 0 ≤ disc z := by
    intro z
    have h1 := hanorm z
    have h2 := (hnpos z).le
    have : 0 ≤ n z * (1 - ((a z).re ^ 2 + (a z).im ^ 2)) := by nlinarith
    have := sq_nonneg (d z)
    simp only [hdisc]
    linarith
  set t : ℂ → ℝ := fun z => (-(d z) + Real.sqrt (disc z)) / n z with ht
  have htc : Continuous t :=
    ((hdc.neg).add (Real.continuous_sqrt.comp hdiscc)).div hnc fun z => (hnpos z).ne'
  set r : ℂ → ℂ := fun z => a z + t z • v z with hr
  have hrc : Continuous r := hac.add (htc.smul hvc)
  have hrre : ∀ z, (r z).re = (a z).re + t z * (v z).re := by intro z; simp [hr]
  have hrim : ∀ z, (r z).im = (a z).im + t z * (v z).im := by intro z; simp [hr]
  have hrnorm : ∀ z, ‖r z‖ = 1 := by
    intro z
    have hsq : (r z).re ^ 2 + (r z).im ^ 2 = 1 := by
      rw [hrre, hrim]
      simpa only [ht, hd, hdisc, hn] using
        alg_root (a z).re (a z).im (v z).re (v z).im (hnpos z) (hanorm z)
    have h1 : ‖r z‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith [hsq]
    nlinarith [norm_nonneg (r z)]
  have hrfix : ∀ z, ‖z‖ = 1 → r z = z := by
    intro z hz
    have haz : a z = z := haid z hz.le
    have hA : z.re ^ 2 + z.im ^ 2 = 1 := by
      have : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
      simpa [Complex.normSq_apply, sq] using this
    have hbz := hbnorm z
    -- `d z ≥ 0` by Cauchy-Schwarz
    have hdnn : 0 ≤ d z := by
      have hdot : z.re * (b z).re + z.im * (b z).im ≤ 1 := by
        nlinarith [sq_nonneg (z.re * (b z).im - z.im * (b z).re),
          sq_nonneg (z.re * (b z).re + z.im * (b z).im - 1)]
      have : d z = 1 - (z.re * (b z).re + z.im * (b z).im) := by
        simp only [hd, hv, haz, Complex.sub_re, Complex.sub_im]
        nlinarith [hA]
      linarith
    have hdiscz : disc z = d z ^ 2 := by
      simp only [hdisc, haz, hA]; ring
    have htz : t z = 0 := by
      simp only [ht, hdiscz, Real.sqrt_sq hdnn]
      simp
    simp [hr, htz, haz]
  exact no_retraction_of_plane_onto_circle r hrc hrnorm hrfix

/-- **Brouwer's fixed point theorem in dimension 2**: every continuous self-map of the
closed unit 2-disk `{x : ℝ² | ‖x‖ ≤ 1}` has a fixed point. -/
