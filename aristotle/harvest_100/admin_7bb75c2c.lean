import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

/-- The squared norm of a complex number, in coordinates. -/
private lemma normSq_coords (x : ℂ) : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- **No retraction theorem** (the form needed here): there is no continuous map `g : ℂ → ℂ`
taking values in the unit circle which restricts to the identity on the unit circle.

The proof lifts `g` through the covering map `Circle.exp : ℝ → Circle`
(`Circle.isCoveringMap_exp`), which is possible because `ℂ` is simply connected and locally
path connected (`IsCoveringMap.existsUnique_continuousMap_lifts`).  The lift, evaluated along
the loop `t ↦ exp (i t)`, differs from `t` by an element of `2 π ℤ`, yet it is `2 π`-periodic;
the intermediate value theorem then produces a value in `2 π ℤ + π`, a contradiction. -/
private lemma no_retraction (g : ℂ → ℂ) (hg : Continuous g) (h1 : ∀ z, ‖g z‖ = 1)
    (hb : ∀ z, ‖z‖ = 1 → g z = z) : False := by
  have hmem : ∀ z : ℂ, g z ∈ Metric.sphere (0 : ℂ) 1 := by
    intro z; simpa [mem_sphere_zero_iff_norm] using h1 z
  set G : C(ℂ, Circle) := ⟨fun z => ⟨g z, hmem z⟩, hg.subtype_mk _⟩ with hG
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts G 0
      (Complex.arg (g 0)) (Circle.exp_arg ⟨g 0, hmem 0⟩)
  have hFlift : ∀ z, Circle.exp (F z) = ⟨g z, hmem z⟩ := fun z => congrFun hF z
  set phi : ℝ → ℝ := fun t => F ((Circle.exp t : Circle) : ℂ) with hphi
  have hphicont : Continuous phi := F.continuous.comp (by fun_prop)
  have key : ∀ t : ℝ, ∃ m : ℤ, phi t = t + m * (2 * π) := by
    intro t
    have hz : g ((Circle.exp t : Circle) : ℂ) = ((Circle.exp t : Circle) : ℂ) := hb _ (by simp)
    have hexp : Circle.exp (phi t) = Circle.exp t := by
      rw [hphi]; simp only []; rw [hFlift]; exact Subtype.ext hz
    exact Circle.exp_eq_exp.mp hexp
  set psi : ℝ → ℝ := fun t => phi t - t with hpsi
  have hpsicont : Continuous psi := hphicont.sub continuous_id
  have hper : phi (2 * π) = phi 0 := by rw [hphi]; norm_num
  have hpi : 0 < π := Real.pi_pos
  have hmem2 : phi 0 - π ∈ Set.Icc (psi (2 * π)) (psi 0) := by
    constructor <;> simp [hpsi, hper] <;> linarith
  obtain ⟨t, -, ht⟩ :=
    intermediate_value_Icc' (by linarith : (0:ℝ) ≤ 2 * π) hpsicont.continuousOn hmem2
  obtain ⟨m, hm⟩ := key t
  obtain ⟨n, hn⟩ := key 0
  rw [hpsi] at ht
  simp only [] at ht
  have h3 : π * ((2 * n - 1 - 2 * m : ℤ) : ℝ) = 0 := by push_cast; linarith
  have h4 : ((2 * n - 1 - 2 * m : ℤ) : ℝ) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h (by positivity)
    · exact h
  have h5 : (2 * n - 1 - 2 * m : ℤ) = 0 := by exact_mod_cast h4
  omega

/-- **Brouwer's fixed point theorem for the closed unit disk in `ℂ`.**

If `f` had no fixed point, the map sending `z` to the point where the ray from `f z` through `z`
meets the unit circle would be a retraction of the disk onto the circle; composing with the
radial retraction of `ℂ` onto the disk contradicts `no_retraction`. -/
theorem brouwer_disk_complex (f : ℂ → ℂ)
    (hf : ContinuousOn f (Metric.closedBall 0 1))
    (hm : Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ z ∈ Metric.closedBall (0 : ℂ) 1, f z = z := by
  by_contra hcon
  push_neg at hcon
  -- the radial retraction of `ℂ` onto the closed unit disk
  set P : ℂ → ℂ := fun z => (max 1 ‖z‖)⁻¹ • z with hPdef
  have hmax : ∀ z : ℂ, (1:ℝ) ≤ max 1 ‖z‖ := fun z => le_max_left _ _
  have hPcont : Continuous P := by
    apply Continuous.smul _ continuous_id
    exact (continuous_const.max continuous_norm).inv₀ fun z => by have := hmax z; linarith
  have hPmem : ∀ z, P z ∈ Metric.closedBall (0:ℂ) 1 := by
    intro z
    have h1 := hmax z
    have h2 : ‖z‖ ≤ max 1 ‖z‖ := le_max_right _ _
    simp only [Metric.mem_closedBall, dist_zero_right, hPdef, norm_smul, norm_inv,
      Real.norm_eq_abs]
    rw [abs_of_pos (by linarith), inv_mul_le_iff₀ (by linarith)]
    linarith
  have hPeq : ∀ z : ℂ, ‖z‖ ≤ 1 → P z = z := by
    intro z hz; simp [hPdef, max_eq_left hz]
  have hfP : Continuous fun z => f (P z) := hf.comp_continuous hPcont hPmem
  -- the direction of the ray, and the coefficients of the quadratic equation determining
  -- its intersection with the unit circle
  set U : ℂ → ℂ := fun z => P z - f (P z) with hUdef
  have hUne : ∀ z, U z ≠ 0 := fun z h => hcon (P z) (hPmem z) (sub_eq_zero.mp h).symm
  have hUcont : Continuous U := hPcont.sub hfP
  set a : ℂ → ℝ := fun z => (U z).re ^ 2 + (U z).im ^ 2 with hadef
  set b : ℂ → ℝ := fun z => (P z).re * (U z).re + (P z).im * (U z).im with hbdef
  set c : ℂ → ℝ := fun z => (P z).re ^ 2 + (P z).im ^ 2 - 1 with hcdef
  set s : ℂ → ℝ := fun z => Real.sqrt (b z ^ 2 - a z * c z) with hsdef
  set t : ℂ → ℝ := fun z => (-(b z) + s z) / a z with htdef
  set g : ℂ → ℂ := fun z => P z + (t z : ℂ) * U z with hgdef
  have hapos : ∀ z, 0 < a z := by
    intro z
    have h : ‖U z‖ ^ 2 = a z := normSq_coords (U z)
    rw [← h]
    have : 0 < ‖U z‖ := norm_pos_iff.mpr (hUne z)
    positivity
  have hcle : ∀ z, c z ≤ 0 := by
    intro z
    have h := hPmem z
    simp only [Metric.mem_closedBall, dist_zero_right] at h
    have := normSq_coords (P z)
    nlinarith [norm_nonneg (P z)]
  have hdisc : ∀ z, 0 ≤ b z ^ 2 - a z * c z := by
    intro z; nlinarith [hapos z, hcle z, sq_nonneg (b z)]
  have hs2 : ∀ z, (s z) ^ 2 = b z ^ 2 - a z * c z := fun z => Real.sq_sqrt (hdisc z)
  have hat : ∀ z, a z * t z = -(b z) + s z := by
    intro z
    simp only [htdef]
    exact mul_div_cancel₀ _ (hapos z).ne'
  have hquad : ∀ z, a z * (t z) ^ 2 + 2 * b z * t z + c z = 0 := by
    intro z
    have h1 : a z * (a z * (t z) ^ 2 + 2 * b z * t z + c z) = 0 := by
      linear_combination (a z * t z + b z + s z) * (hat z) + (hs2 z)
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (hapos z).ne'
    · exact h2
  -- `g` maps into the unit circle
  have hgnorm : ∀ z, ‖g z‖ = 1 := by
    intro z
    have hsq : ‖g z‖ ^ 2 = 1 := by
      rw [normSq_coords]
      simp only [hgdef, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      have h := hquad z
      simp only [hadef, hbdef, hcdef] at h
      nlinarith [h]
    nlinarith [norm_nonneg (g z), hsq]
  -- `g` is continuous
  have hacont : Continuous a := by rw [hadef]; fun_prop
  have hbcont : Continuous b := by rw [hbdef]; fun_prop
  have hccont : Continuous c := by rw [hcdef]; fun_prop
  have hscont : Continuous s := by
    rw [hsdef]; exact Real.continuous_sqrt.comp (by fun_prop)
  have htcont : Continuous t := by
    rw [htdef]
    exact ((continuous_neg.comp hbcont).add hscont).div hacont fun z => (hapos z).ne'
  have hgcont : Continuous g := by
    rw [hgdef]
    exact hPcont.add ((Complex.continuous_ofReal.comp htcont).mul hUcont)
  -- `g` is the identity on the unit circle
  have hgbdry : ∀ z : ℂ, ‖z‖ = 1 → g z = z := by
    intro z hz
    have hPz : P z = z := hPeq z hz.le
    have hcz : c z = 0 := by
      simp only [hcdef, hPz]
      have := normSq_coords z
      rw [hz] at this
      linarith
    have hfz : ‖f z‖ ≤ 1 := by
      have h := hm (hPmem z)
      rw [hPz] at h
      simpa [Metric.mem_closedBall, dist_zero_right] using h
    have hbnn : 0 ≤ b z := by
      simp only [hbdef, hUdef, hPz, Complex.sub_re, Complex.sub_im]
      have h1 := normSq_coords z
      rw [hz] at h1
      have h2 := normSq_coords (f z)
      have h3 : ‖f z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (f z)]
      nlinarith [sq_nonneg (z.re - (f z).re), sq_nonneg (z.im - (f z).im)]
    have hsz : s z = b z := by
      simp only [hsdef, hcz, mul_zero, sub_zero]
      exact Real.sqrt_sq hbnn
    have htz : t z = 0 := by simp only [htdef, hsz]; ring_nf
    simp only [hgdef, htz, Complex.ofReal_zero, zero_mul, add_zero, hPz]
  exact no_retraction g hgcont hgnorm hgbdry

/-- **Brouwer's fixed point theorem in dimension two**: every continuous self-map of the closed
2-disk `{x : ℝ² | ‖x‖ ≤ 1}` has a fixed point. -/
theorem brouwer_2d (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : ContinuousOn f (Metric.closedBall 0 1))
    (hm : Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f x = x := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ) with hedef
  have hmemiff : ∀ z : ℂ, z ∈ Metric.closedBall (0:ℂ) 1 ↔
      e z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z
    simp [Metric.mem_closedBall, dist_zero_right, e.norm_map]
  set F : ℂ → ℂ := fun z => e.symm (f (e z)) with hFdef
  have hmapsE : Set.MapsTo (fun z : ℂ => e z) (Metric.closedBall 0 1)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := fun z hz => (hmemiff z).mp hz
  have hFcont : ContinuousOn F (Metric.closedBall 0 1) := by
    apply (e.symm.continuous).comp_continuousOn
    exact hf.comp e.continuous.continuousOn hmapsE
  have hFmaps : Set.MapsTo F (Metric.closedBall 0 1) (Metric.closedBall (0:ℂ) 1) := by
    intro z hz
    have := hm (hmapsE hz)
    rw [hmemiff]
    simpa [hFdef] using this
  obtain ⟨z, hz, hfz⟩ := brouwer_disk_complex F hFcont hFmaps
  refine ⟨e z, (hmemiff z).mp hz, ?_⟩
  have := congrArg (fun w : ℂ => e w) hfz
  simpa [hFdef] using this

end Math

