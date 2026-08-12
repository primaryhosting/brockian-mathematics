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

namespace BrouwerAux

/-- The radial retraction of the plane `ℂ` onto the closed unit disk. -/
noncomputable def proj (z : ℂ) : ℂ := (max 1 ‖z‖)⁻¹ • z

lemma one_le_max_norm_pos (z : ℂ) : (0:ℝ) < max 1 ‖z‖ :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

lemma continuous_proj : Continuous proj := by
  apply Continuous.smul _ continuous_id
  exact (continuous_const.max continuous_norm).inv₀ (fun z => (one_le_max_norm_pos z).ne')

lemma norm_proj_le (z : ℂ) : ‖proj z‖ ≤ 1 := by
  rw [proj, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (one_le_max_norm_pos z),
    inv_mul_le_iff₀ (one_le_max_norm_pos z), mul_one]
  exact le_max_right _ _

lemma proj_eq_self {z : ℂ} (h : ‖z‖ ≤ 1) : proj z = z := by
  rw [proj, max_eq_left h, inv_one, one_smul]

/-- There is no continuous retraction of the plane onto the unit circle. -/
theorem no_retraction (R : ℂ → ℂ) (hR : Continuous R) (hnorm : ∀ z, ‖R z‖ = 1)
    (hfix : ∀ z, ‖z‖ = 1 → R z = z) : False := by
  have hmem : ∀ z : ℂ, R z ∈ Submonoid.unitSphere ℂ := by
    intro z; simp [Submonoid.unitSphere, hnorm z]
  set Rc : C(ℂ, Circle) := ⟨fun z => ⟨R z, hmem z⟩, hR.subtype_mk _⟩ with hRc
  have hR1 : R 1 = 1 := hfix 1 (by simp)
  have he : Circle.exp 0 = Rc 1 := by
    apply Circle.ext
    simp [hRc, hR1]
  obtain ⟨θ, ⟨hθ1, hθlift⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts Rc (1 : ℂ) (0 : ℝ) he
  set u : ℝ → ℝ := fun t => θ ((Circle.exp t : Circle) : ℂ) with hu
  have hcoe : Continuous (fun t : ℝ => ((Circle.exp t : Circle) : ℂ)) :=
    continuous_subtype_val.comp Circle.exp.continuous
  have hucont : Continuous u := θ.continuous.comp hcoe
  have hcomp : Circle.exp ∘ u = Circle.exp ∘ id := by
    funext t
    have h1 : ‖((Circle.exp t : Circle) : ℂ)‖ = 1 := Circle.norm_coe _
    have h2 := congrFun hθlift ((Circle.exp t : Circle) : ℂ)
    simp only [Function.comp_apply] at h2 ⊢
    rw [h2]
    apply Circle.ext
    simpa [hRc] using hfix _ h1
  have hu0 : u 0 = id 0 := by simpa [hu] using hθ1
  have hid := Circle.isCoveringMap_exp.eq_of_comp_eq hucont continuous_id hcomp 0 hu0
  have h2pi : u (2 * π) = 2 * π := by rw [hid]; rfl
  have hz : u (2 * π) = 0 := by
    have hper : Circle.exp (2 * π) = Circle.exp 0 := by simp
    rw [hu]
    simp [hper, hθ1]
  rw [hz] at h2pi
  have := Real.pi_pos
  linarith

lemma sqnorm (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

lemma norm_add_smul_sq (w v : ℂ) (t : ℝ) :
    ‖w + (t : ℂ) * v‖ ^ 2 = ‖w‖ ^ 2 + 2 * t * (w.re * v.re + w.im * v.im) + t ^ 2 * ‖v‖ ^ 2 := by
  rw [sqnorm, sqnorm, sqnorm]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma quad_root (a b c s t : ℝ) (ha : a ≠ 0) (hs : s ^ 2 = b ^ 2 + a * c)
    (ht : t = (-b + s) / a) : 2 * t * b + t ^ 2 * a = c := by
  subst ht; field_simp; linear_combination hs

/-- If a continuous self-map of the closed unit disk (precomposed with the radial retraction)
has no fixed point, one can build a retraction of the plane onto the unit circle. -/
theorem exists_retraction (g : ℂ → ℂ) (hg : Continuous g) (hgb : ∀ z, ‖g z‖ ≤ 1)
    (hne : ∀ z, g z ≠ proj z) :
    ∃ R : ℂ → ℂ, Continuous R ∧ (∀ z, ‖R z‖ = 1) ∧ (∀ z, ‖z‖ = 1 → R z = z) := by
  set w : ℂ → ℂ := proj with hwdef
  set v : ℂ → ℂ := fun z => w z - g z with hvdef
  have hvpos : ∀ z, 0 < ‖v z‖ := fun z => norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm (hne z)))
  set B : ℂ → ℝ := fun z => (w z).re * (v z).re + (w z).im * (v z).im with hBdef
  set A : ℂ → ℝ := fun z => ‖v z‖ ^ 2 with hAdef
  have hA : ∀ z, 0 < A z := fun z => pow_pos (hvpos z) 2
  set C : ℂ → ℝ := fun z => 1 - ‖w z‖ ^ 2 with hCdef
  have hC : ∀ z, 0 ≤ C z := by
    intro z
    have h1 := norm_proj_le z
    have h2 := norm_nonneg (w z)
    simp only [hCdef]
    nlinarith
  set S : ℂ → ℝ := fun z => Real.sqrt (B z ^ 2 + A z * C z) with hSdef
  have hS2 : ∀ z, S z ^ 2 = B z ^ 2 + A z * C z := by
    intro z
    apply Real.sq_sqrt
    nlinarith [sq_nonneg (B z), (hA z).le, hC z]
  set T : ℂ → ℝ := fun z => (-B z + S z) / A z with hTdef
  have hkey : ∀ z, ‖w z + (T z : ℂ) * v z‖ ^ 2 = 1 := by
    intro z
    rw [norm_add_smul_sq]
    have h := quad_root (A z) (B z) (C z) (S z) (T z) (hA z).ne' (hS2 z) rfl
    simp only [hAdef] at h ⊢
    simp only [hCdef] at *
    linarith [h]
  have hwc : Continuous w := continuous_proj
  have hvc : Continuous v := hwc.sub hg
  have hBc : Continuous B :=
    ((Complex.continuous_re.comp hwc).mul (Complex.continuous_re.comp hvc)).add
      ((Complex.continuous_im.comp hwc).mul (Complex.continuous_im.comp hvc))
  have hAc : Continuous A := hvc.norm.pow 2
  have hCc : Continuous C := continuous_const.sub (hwc.norm.pow 2)
  have hSc : Continuous S := Real.continuous_sqrt.comp ((hBc.pow 2).add (hAc.mul hCc))
  have hTc : Continuous T := (hBc.neg.add hSc).div hAc (fun z => (hA z).ne')
  refine ⟨fun z => w z + (T z : ℂ) * v z, hwc.add ((Complex.continuous_ofReal.comp hTc).mul hvc),
    ?_, ?_⟩
  · intro z
    nlinarith [norm_nonneg (w z + (T z : ℂ) * v z), hkey z]
  · intro z hz
    have hwz : w z = z := proj_eq_self hz.le
    have hCz : C z = 0 := by simp [hCdef, hwz, hz]
    have hBz : 0 ≤ B z := by
      have hgz : ‖g z‖ ^ 2 ≤ 1 := by nlinarith [hgb z, norm_nonneg (g z)]
      rw [sqnorm] at hgz
      have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by rw [← sqnorm, hz]; norm_num
      simp only [hBdef, hvdef, hwz, Complex.sub_re, Complex.sub_im]
      nlinarith [sq_nonneg (z.re * (g z).im - z.im * (g z).re),
        sq_nonneg (z.re * (g z).re + z.im * (g z).im - 1)]
    have hSz : S z = B z := by
      simp only [hSdef, hCz, mul_zero, add_zero]
      rw [Real.sqrt_sq hBz]
    have hTz : T z = 0 := by simp [hTdef, hSz]
    simp [hTz, hwz]

/-- Brouwer's fixed point theorem for the closed unit disk in `ℂ`. -/
theorem brouwer_complex {f : ℂ → ℂ} (hf : ContinuousOn f (Metric.closedBall 0 1))
    (hmap : Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ z ∈ Metric.closedBall (0 : ℂ) 1, f z = z := by
  by_contra hcon
  push_neg at hcon
  have hmem : ∀ z : ℂ, proj z ∈ Metric.closedBall (0 : ℂ) 1 := fun z => by
    simpa [Metric.mem_closedBall, dist_zero_right] using norm_proj_le z
  have hgc : Continuous (fun z => f (proj z)) := hf.comp_continuous continuous_proj hmem
  have hgb : ∀ z, ‖f (proj z)‖ ≤ 1 := fun z => by
    simpa [Metric.mem_closedBall, dist_zero_right] using hmap (hmem z)
  have hne : ∀ z, f (proj z) ≠ proj z := fun z => hcon _ (hmem z)
  obtain ⟨R, hRc, hRn, hRfix⟩ := exists_retraction (fun z => f (proj z)) hgc hgb hne
  exact no_retraction R hRc hRn hRfix

end BrouwerAux

namespace Math

/-- **Brouwer's fixed point theorem in dimension two**: every continuous self-map of the
closed 2-disk has a fixed point. -/
theorem brouwer_2d {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : ContinuousOn f (Metric.closedBall 0 1))
    (hmap : Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f x = x := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr with he
  have hemem : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) 1 →
      e z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    simpa [e.norm_map] using hz
  have hFcont : ContinuousOn (fun z : ℂ => e.symm (f (e z))) (Metric.closedBall 0 1) :=
    e.symm.continuous.comp_continuousOn
      (hf.comp e.continuous.continuousOn (fun z hz => hemem z hz))
  have hFmap : Set.MapsTo (fun z : ℂ => e.symm (f (e z))) (Metric.closedBall 0 1)
      (Metric.closedBall 0 1) := by
    intro z hz
    have h1 := hmap (hemem z hz)
    simp only [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
    simpa [e.symm.norm_map] using h1
  obtain ⟨z, hz, hfz⟩ := BrouwerAux.brouwer_complex hFcont hFmap
  refine ⟨e z, hemem z hz, ?_⟩
  have := congrArg e hfz
  simpa using this

end Math

