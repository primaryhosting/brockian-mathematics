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
theorem alg_root (ar ai vr vi : ℝ) (hN : 0 < vr ^ 2 + vi ^ 2) (hA : ar ^ 2 + ai ^ 2 ≤ 1) :
    (ar + ((-(ar * vr + ai * vi) +
        Real.sqrt ((ar * vr + ai * vi) ^ 2 + (vr ^ 2 + vi ^ 2) * (1 - (ar ^ 2 + ai ^ 2))))
        / (vr ^ 2 + vi ^ 2)) * vr) ^ 2
    + (ai + ((-(ar * vr + ai * vi) +
        Real.sqrt ((ar * vr + ai * vi) ^ 2 + (vr ^ 2 + vi ^ 2) * (1 - (ar ^ 2 + ai ^ 2))))
        / (vr ^ 2 + vi ^ 2)) * vi) ^ 2 = 1 := by
  set d := ar * vr + ai * vi with hd
  set N := vr ^ 2 + vi ^ 2 with hNdef
  set A := ar ^ 2 + ai ^ 2 with hAdef
  have hnn : 0 ≤ d ^ 2 + N * (1 - A) := by nlinarith [sq_nonneg d]
  set s := Real.sqrt (d ^ 2 + N * (1 - A)) with hsdef
  have hs : s ^ 2 = d ^ 2 + N * (1 - A) := Real.sq_sqrt hnn
  have hNne : N ≠ 0 := ne_of_gt hN
  field_simp
  nlinarith [hs, sq_nonneg (s - d), sq_nonneg N]

/-- There is no continuous retraction of the plane onto the unit circle:
if `r : ℂ → ℂ` is continuous with `‖r z‖ = 1` for all `z` and `r z = z` whenever `‖z‖ = 1`,
we get a contradiction.  The proof lifts `r` through the covering map
`Circle.exp : ℝ → Circle` (using that `ℂ` is simply connected) and computes winding numbers. -/
theorem no_retraction_of_plane_onto_circle (r : ℂ → ℂ) (hr : Continuous r)
    (hnorm : ∀ z, ‖r z‖ = 1) (hfix : ∀ z, ‖z‖ = 1 → r z = z) : False := by
  have hmem : ∀ z : ℂ, r z ∈ Metric.sphere (0 : ℂ) 1 := by
    intro z; simp [hnorm z]
  let R : C(ℂ, Circle) := ⟨fun z => ⟨r z, hmem z⟩, Continuous.subtype_mk hr _⟩
  obtain ⟨g, ⟨-, hg⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts R 0
    (Complex.arg (R 0)) (Circle.exp_arg _)
  have key : ∀ t : ℝ, Circle.exp (g (Complex.exp (t * I))) = Circle.exp t := by
    intro t
    have h1 : Circle.exp (g (Complex.exp (t * I))) = R (Complex.exp (t * I)) := congrFun hg _
    rw [h1]
    apply Subtype.ext
    show r (Complex.exp (t * I)) = _
    rw [hfix _ (Complex.norm_exp_ofReal_mul_I t), Circle.coe_exp]
  set φ : ℝ → ℝ := fun t => g (Complex.exp (t * I)) with hφ
  have hφc : Continuous φ := by
    apply g.continuous.comp; fun_prop
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hint : ∀ t : ℝ, ∃ n : ℤ, φ t - t = n * (2 * Real.pi) := by
    intro t
    rw [← Circle.exp_eq_one, Circle.exp_sub, key t, div_self']
  set ψ : ℝ → ℝ := fun t => (φ t - t) / (2 * Real.pi) with hψ
  have hψc : Continuous ψ := by fun_prop
  have hψint : ∀ t, ∃ n : ℤ, ψ t = n := by
    intro t
    obtain ⟨n, hn⟩ := hint t
    refine ⟨n, ?_⟩
    rw [hψ]
    field_simp [hn]
    linarith [hn]
  have hper : φ (2 * Real.pi) = φ 0 := by simp [hφ]
  have hend : ψ (2 * Real.pi) = ψ 0 - 1 := by
    rw [hψ]; simp only [hper]; field_simp; ring
  obtain ⟨m, hm⟩ := hψint 0
  have hmem2 : ψ 0 - 1 / 2 ∈ Set.Icc (ψ (2 * Real.pi)) (ψ 0) := by
    rw [hend]; constructor <;> linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc' hpi.le hψc.continuousOn hmem2
  obtain ⟨n, hn⟩ := hψint t
  rw [hn, hm] at ht
  have h2 : (2 * n : ℝ) = 2 * m - 1 := by linarith
  have h3 : (2 * n : ℤ) = 2 * m - 1 := by exact_mod_cast h2
  omega

/-- **Brouwer's fixed point theorem in dimension 2**, complex-plane version:
every continuous self-map of the closed unit disk in `ℂ` has a fixed point. -/
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
theorem brouwer_2d (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : ContinuousOn f (Metric.closedBall 0 1))
    (hmaps : Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f x = x := by
  set e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
    (Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)).symm
  have hmapsymm : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) 1 →
      e.symm z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    simpa using hz
  have hmape : ∀ x : EuclideanSpace ℝ (Fin 2), x ∈ Metric.closedBall (0 : _) 1 →
      e x ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    simpa using hx
  set F : ℂ → ℂ := fun z => e (f (e.symm z))
  have hFcont : ContinuousOn F (Metric.closedBall 0 1) := by
    refine e.continuous.comp_continuousOn (hf.comp e.symm.continuous.continuousOn ?_)
    intro z hz
    exact hmapsymm z hz
  have hFmaps : Set.MapsTo F (Metric.closedBall (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    exact hmape _ (hmaps (hmapsymm z hz))
  obtain ⟨z, hz, hfz⟩ := brouwer_complex F hFcont hFmaps
  refine ⟨e.symm z, hmapsymm z hz, ?_⟩
  have : e (f (e.symm z)) = z := hfz
  calc f (e.symm z) = e.symm (e (f (e.symm z))) := by simp
    _ = e.symm z := by rw [this]

/-- **Brouwer's fixed point theorem in dimension 2**, bundled version: every continuous
self-map of the closed unit disk `D ⊆ ℝ²`, viewed as a topological space in its own right,
has a fixed point. -/
theorem brouwer_2d_disk
    (f : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (hf : Continuous f) :
    ∃ x, f x = x := by
  have hmem : ∀ x : EuclideanSpace ℝ (Fin 2),
      (max 1 ‖x‖)⁻¹ • x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro x
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul]
    have h1 : (1 : ℝ) ≤ max 1 ‖x‖ := le_max_left _ _
    have h2 : ‖x‖ ≤ max 1 ‖x‖ := le_max_right _ _
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith), inv_mul_le_iff₀ (by linarith)]
    linarith
  set proj : EuclideanSpace ℝ (Fin 2) → Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun x => ⟨(max 1 ‖x‖)⁻¹ • x, hmem x⟩ with hproj
  have hprojc : Continuous proj := by
    apply Continuous.subtype_mk
    refine Continuous.smul ((continuous_const.max continuous_norm).inv₀ ?_) continuous_id
    intro x
    have : (1 : ℝ) ≤ max 1 ‖x‖ := le_max_left _ _
    linarith
  set g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun x => (f (proj x) : EuclideanSpace ℝ (Fin 2))
  have hgc : Continuous g := continuous_subtype_val.comp (hf.comp hprojc)
  obtain ⟨x, hx, hgx⟩ := brouwer_2d g hgc.continuousOn (fun x _ => (f (proj x)).2)
  have hxle : ‖x‖ ≤ 1 := by simpa using hx
  have hpx : proj x = ⟨x, hx⟩ := Subtype.ext (by simp [hproj, max_eq_left hxle])
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  show (f ⟨x, hx⟩ : EuclideanSpace ℝ (Fin 2)) = x
  rw [← hpx]
  exact hgx

end Math

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

