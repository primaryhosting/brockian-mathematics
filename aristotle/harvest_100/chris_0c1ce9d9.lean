/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set Complex

namespace Math

noncomputable section

/-! ## Step 1: the radial projection onto the closed unit disk of `ℂ`. -/

/-- Radial projection of `ℂ` onto the closed unit disk. -/
noncomputable def proj (z : ℂ) : ℂ := (max 1 ‖z‖)⁻¹ • z

lemma continuous_proj : Continuous proj := by
  apply Continuous.smul _ continuous_id
  exact (continuous_const.max continuous_norm).inv₀ (fun z => by positivity)

lemma norm_proj_le (z : ℂ) : ‖proj z‖ ≤ 1 := by
  have h1 : (1:ℝ) ≤ max 1 ‖z‖ := le_max_left _ _
  have h2 : ‖z‖ ≤ max 1 ‖z‖ := le_max_right _ _
  rw [proj, norm_smul]
  simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ max 1 ‖z‖)]
  rw [inv_mul_le_iff₀ (by linarith)]
  linarith

lemma proj_eq_self {z : ℂ} (hz : ‖z‖ ≤ 1) : proj z = z := by
  rw [proj, max_eq_left hz]
  simp

/-! ## Step 2: no continuous retraction of `ℂ` onto the unit circle. -/

/-- There is no continuous map `ℂ → ℂ` with values in the unit circle which is the
identity on the unit circle. -/
theorem no_retraction (g : ℂ → ℂ) (hg : Continuous g) (hnorm : ∀ z, ‖g z‖ = 1)
    (hbdry : ∀ z, ‖z‖ = 1 → g z = z) : False := by
  -- Upgrade `g` to a continuous map into the circle.
  have hmem : ∀ z : ℂ, g z ∈ Submonoid.unitSphere ℂ := by
    intro z
    simpa [Submonoid.unitSphere, mem_sphere_iff_norm] using hnorm z
  let G : C(ℂ, Circle) := ⟨fun z => ⟨g z, hmem z⟩, by fun_prop⟩
  -- Since `ℂ` is simply connected and locally path connected, `G` lifts along the
  -- covering map `Circle.exp : ℝ → Circle`.
  obtain ⟨F, ⟨-, hFlift⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      G 0 (Complex.arg ((G 0 : Circle) : ℂ)) (Circle.exp_arg (G 0))
  -- The boundary circle, parametrized by angle.
  set w : ℝ → ℂ := fun s => ((Circle.exp s : Circle) : ℂ) with hw
  have hwc : Continuous w := by fun_prop
  have hwnorm : ∀ s, ‖w s‖ = 1 := fun s => Circle.norm_coe _
  have hGw : ∀ s, G (w s) = Circle.exp s := fun s =>
    Circle.coe_inj.mp (hbdry (w s) (hwnorm s))
  -- The lift differs from the angle by an integer multiple of `2 * π`.
  have key : ∀ s : ℝ, ∃ m : ℤ, F (w s) = s + m * (2 * Real.pi) := by
    intro s
    rw [← Circle.exp_eq_exp]
    have hFs : Circle.exp (F (w s)) = G (w s) := congrFun hFlift (w s)
    rw [hFs, hGw s]
  have hw0 : w (2 * Real.pi) = w 0 := by
    have : Circle.exp (2 * Real.pi) = Circle.exp 0 :=
      Circle.exp_eq_exp.mpr ⟨1, by push_cast; ring⟩
    simp only [hw, this]
  -- The normalized difference is a continuous integer-valued function, which is
  -- impossible since it drops by exactly `1` along the loop.
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  set h : ℝ → ℝ := fun s => (F (w s) - s) / (2 * Real.pi) with hh
  have hcont : Continuous h := by fun_prop
  have hint : ∀ s, ∃ m : ℤ, h s = m := by
    intro s
    obtain ⟨m, hm⟩ := key s
    refine ⟨m, ?_⟩
    have hd : F (w s) - s = (m:ℝ) * (2*Real.pi) := by rw [hm]; ring
    simp only [hh, hd]
    field_simp
  have hend : h (2 * Real.pi) = h 0 - 1 := by
    simp only [hh, hw0]
    field_simp
    ring
  obtain ⟨k, hk⟩ := hint 0
  have hsub := intermediate_value_uIcc (f := h) (a := (0:ℝ)) (b := 2*Real.pi) hcont.continuousOn
  obtain ⟨s, -, hs⟩ := hsub (show (k:ℝ) - 1/2 ∈ uIcc (h 0) (h (2*Real.pi)) by
    rw [Set.mem_uIcc]; right; rw [hend, hk]; constructor <;> linarith)
  obtain ⟨m, hm⟩ := hint s
  rw [hm] at hs
  have h2 : (2*m + 1 : ℤ) = 2*k := by
    have : ((2*m+1 : ℤ) : ℝ) = ((2*k : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

/-! ## Step 3: a fixed-point-free self map of the disk yields a retraction. -/

/-- If a continuous self-map `f` of the closed unit disk has no fixed point, then the map
sending `z` to the point where the ray from `f z` through `z` meets the unit circle is a
continuous retraction of `ℂ` onto the unit circle. -/
theorem exists_retraction_of_no_fixed_point (f : ℂ → ℂ)
    (hf : ContinuousOn f (closedBall 0 1)) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1))
    (hnofix : ∀ x ∈ closedBall (0 : ℂ) 1, f x ≠ x) :
    ∃ g : ℂ → ℂ, Continuous g ∧ (∀ z, ‖g z‖ = 1) ∧ (∀ z, ‖z‖ = 1 → g z = z) := by
  have hmemy : ∀ z : ℂ, proj z ∈ closedBall (0:ℂ) 1 := fun z =>
    mem_closedBall_zero_iff.mpr (norm_proj_le z)
  set P : ℂ → ℂ := fun z => proj z
  set Q : ℂ → ℂ := fun z => f (proj z)
  have hQcont : Continuous Q := hf.comp_continuous continuous_proj hmemy
  have hQnorm : ∀ z, ‖Q z‖ ≤ 1 := fun z => mem_closedBall_zero_iff.mp (hmaps (hmemy z))
  set d : ℂ → ℂ := fun z => P z - Q z
  have hdeq : ∀ z, d z = P z - Q z := fun z => rfl
  have hdne : ∀ z, d z ≠ 0 := by
    intro z hz
    refine hnofix (proj z) (hmemy z) ?_
    have : P z = Q z := by rw [hdeq] at hz; rwa [sub_eq_zero] at hz
    exact this.symm
  have hdnorm : ∀ z, ‖d z‖ ≠ 0 := fun z => norm_ne_zero_iff.mpr (hdne z)
  -- the unit vector pointing from `f z` to `z`
  set u : ℂ → ℂ := fun z => ‖d z‖⁻¹ • d z
  have hueq : ∀ z, u z = ‖d z‖⁻¹ • d z := fun z => rfl
  have hunorm : ∀ z, ‖u z‖ = 1 := by
    intro z
    rw [hueq z, norm_smul]
    simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (hdnorm z)
  set A : ℂ → ℝ := fun z => inner ℝ (P z) (u z)
  have hAeq : ∀ z, A z = inner ℝ (P z) (u z) := fun z => rfl
  -- the distance one has to travel from `z` in direction `u z` to reach the unit circle
  set T : ℂ → ℝ := fun z => -A z + Real.sqrt ((A z)^2 + 1 - ‖P z‖^2)
  have hTeq : ∀ z, T z = -A z + Real.sqrt ((A z)^2 + 1 - ‖P z‖^2) := fun z => rfl
  refine ⟨fun z => P z + T z • u z, ?_, ?_, ?_⟩
  · have hPc : Continuous P := continuous_proj
    have hdc : Continuous d := hPc.sub hQcont
    have huc : Continuous u := Continuous.smul ((hdc.norm).inv₀ hdnorm) hdc
    have hAc : Continuous A := hPc.inner huc
    have hTc : Continuous T :=
      Continuous.add hAc.neg (((hAc.pow 2).add continuous_const).sub (hPc.norm.pow 2)).sqrt
    exact hPc.add (hTc.smul huc)
  · intro z
    have hD : 0 ≤ (A z)^2 + 1 - ‖P z‖^2 := by
      have := norm_proj_le z
      nlinarith [sq_nonneg (A z), norm_nonneg (P z)]
    have hS : (Real.sqrt ((A z)^2 + 1 - ‖P z‖^2))^2 = (A z)^2 + 1 - ‖P z‖^2 := Real.sq_sqrt hD
    have hsq : ‖P z + T z • u z‖^2 = 1 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul]
      simp only [Real.norm_eq_abs, sq_abs, hunorm z, mul_one, ← hAeq z]
      rw [hTeq z]
      nlinarith [hS]
    show ‖P z + T z • u z‖ = 1
    nlinarith [norm_nonneg (P z + T z • u z), hsq]
  · intro z hz
    have hPz : P z = z := proj_eq_self (le_of_eq hz)
    have hAnn : 0 ≤ A z := by
      have h1 : (inner ℝ z (Q z) : ℝ) ≤ 1 := by
        have := real_inner_le_norm z (Q z)
        have h2 := hQnorm z
        nlinarith [norm_nonneg (Q z)]
      have hAz : A z = ‖d z‖⁻¹ * (‖z‖^2 - inner ℝ z (Q z)) := by
        rw [hAeq z, hueq z, real_inner_smul_right, hdeq z, inner_sub_right,
          real_inner_self_eq_norm_sq, hPz]
      rw [hAz, hz]
      have hpos : (0:ℝ) < ‖d z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hdnorm z))
      have hinv : 0 < ‖d z‖⁻¹ := by positivity
      nlinarith
    have hTz : T z = 0 := by
      rw [hTeq z, hPz, hz]
      have h3 : (A z)^2 + 1 - 1^2 = (A z)^2 := by ring
      rw [h3, Real.sqrt_sq hAnn]
      ring
    show P z + T z • u z = z
    rw [hTz, hPz]
    simp

/-- **Brouwer's fixed point theorem** in the complex plane. -/
theorem brouwer_disk_complex (f : ℂ → ℂ) (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : ℂ) 1, f x = x := by
  by_contra h
  push_neg at h
  obtain ⟨g, hg, hnorm, hbdry⟩ := exists_retraction_of_no_fixed_point f hf hmaps h
  exact no_retraction g hg hnorm hbdry

/-- **Brouwer's fixed point theorem in dimension 2**: every continuous self-map of the
closed 2-dimensional disk has a fixed point. -/
theorem brouwer_2d (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f x = x := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr with he
  have hball : ∀ z : ℂ, z ∈ closedBall (0:ℂ) 1 →
      e z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff] at *
    simpa using hz
  have hball' : ∀ y : EuclideanSpace ℝ (Fin 2), y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      e.symm y ∈ closedBall (0:ℂ) 1 := by
    intro y hy
    rw [mem_closedBall_zero_iff] at *
    simpa using hy
  obtain ⟨x, hx, hfx⟩ := brouwer_disk_complex (fun z => e.symm (f (e z)))
    (e.symm.continuous.comp_continuousOn
      (hf.comp e.continuous.continuousOn (fun z hz => hball z hz)))
    (fun z hz => hball' _ (hmaps (hball z hz)))
  refine ⟨e x, hball x hx, ?_⟩
  simpa using congrArg e hfx

/-- **Brouwer's fixed point theorem in dimension 2**, stated for a continuous self-map of the
closed 2-disk regarded as a topological space in its own right. -/
theorem brouwer_2d_subtype (f : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 →
    closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (hf : Continuous f) : ∃ x, f x = x := by
  classical
  set F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun y => if h : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 then
      (f ⟨y, h⟩ : EuclideanSpace ℝ (Fin 2)) else 0 with hF
  have hres : (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).restrict F =
      fun x => (f x : EuclideanSpace ℝ (Fin 2)) := by
    funext x
    simp only [Set.restrict_apply, hF, dif_pos x.2]
  have hFcont : ContinuousOn F (closedBall 0 1) := by
    rw [continuousOn_iff_continuous_restrict, hres]
    exact continuous_subtype_val.comp hf
  have hmapsF : MapsTo F (closedBall 0 1) (closedBall 0 1) := by
    intro y hy
    simp only [hF, dif_pos hy]
    exact (f ⟨y, hy⟩).2
  obtain ⟨x, hx, hfx⟩ := brouwer_2d F hFcont hmapsF
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [hF] at hfx
  simp only [dif_pos hx] at hfx
  exact hfx

end

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

