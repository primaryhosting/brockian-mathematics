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

Every continuous self-map of the closed 2-disk has a fixed point.

Mathlib does not contain Brouwer's fixed point theorem, so it is developed here.  The proof is the
classical degree-theoretic argument, carried out through the homotopy lifting property for
covering maps (`IsCoveringMap.liftHomotopy`) applied to the covering `Circle.exp : ℝ → Circle`:

* `Math.sub_eq_sub_of_circleExp_eq`: two continuous real functions on a preconnected space with
  the same image under `Circle.exp` differ by a constant (lifts are unique up to a constant).
* `Math.lift_endpoint_eq_of_homotopy_from_const`: if a homotopy of loops in the circle starts at
  a constant loop, then any continuous lift of its terminal loop has equal endpoints, i.e. the
  terminal loop has winding number `0`.
* `Math.brouwer_2d_complex`: if a continuous self-map `f` of the closed unit disk in `ℂ` had no
  fixed point, then `v z = (z - f z)/‖z - f z‖` would define a map of the disk into the circle;
  restricted to the boundary circle it is never antipodal to the identity, so it has winding
  number `1`, contradicting the previous lemma applied to the homotopy `(t, s) ↦ v (t e^{2πis})`.
* `Math.brouwer_2d`: transported to `EuclideanSpace ℝ (Fin 2)` along the linear isometry
  equivalence `Complex.orthonormalBasisOneI.repr`.
-/

namespace Math

open Complex Metric Set unitInterval

/-- Two continuous real functions on a preconnected space whose images under `Circle.exp` agree
differ by a constant. -/
theorem sub_eq_sub_of_circleExp_eq {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {θ φ : X → ℝ} (hθ : Continuous θ) (hφ : Continuous φ)
    (h : ∀ x, Circle.exp (θ x) = Circle.exp (φ x)) (x y : X) :
    θ x - φ x = θ y - φ y := by
  set g : X → ℝ := fun z => θ z - φ z with hg
  have hgc : Continuous g := hθ.sub hφ
  have hint : ∀ z, ∃ m : ℤ, g z = m * (2 * Real.pi) := by
    intro z
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (h z)
    exact ⟨m, by simp [hg, hm]⟩
  have hpi := Real.pi_pos
  have key : ∀ a b : X, ¬ (g a < g b) := by
    intro a b hlt
    obtain ⟨m, hm⟩ := hint a
    obtain ⟨n, hn⟩ := hint b
    have hmn : (m : ℝ) < n := by nlinarith
    have hmn' : m < n := by exact_mod_cast hmn
    have h1 : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn'
    have hle : g a + Real.pi ≤ g b := by nlinarith
    obtain ⟨z, hz⟩ := intermediate_value_univ a b hgc
      (show g a + Real.pi ∈ Icc (g a) (g b) from ⟨by linarith, hle⟩)
    obtain ⟨k, hk⟩ := hint z
    rw [hk, hm] at hz
    have hhalf : (2 * (k - m) : ℝ) = 1 := by
      have : ((k : ℝ) - m) * (2 * Real.pi) = Real.pi := by linarith
      nlinarith
    have : (2 * (k - m) : ℤ) = 1 := by exact_mod_cast hhalf
    omega
  have h1 := key x y
  have h2 := key y x
  simp only [not_lt] at h1 h2
  linarith

/-- If a homotopy of loops `H` in the circle starts at a constant loop, then any continuous
lift of its terminal loop has equal endpoints. -/
theorem lift_endpoint_eq_of_homotopy_from_const (H : C(I × I, Circle))
    (hconst : ∀ s : I, H (0, s) = H (0, 0))
    (hloop : ∀ t : I, H (t, 0) = H (t, 1))
    (θ : I → ℝ) (hθ : Continuous θ) (hlift : ∀ s : I, Circle.exp (θ s) = H (1, s)) :
    θ 1 = θ 0 := by
  set c : ℝ := Complex.arg ((H (0, 0) : Circle) : ℂ) with hc
  have H_0 : ∀ a : I, H (0, a) = Circle.exp c := by
    intro a; rw [hconst a, hc, Circle.exp_arg]
  set F : C(I, ℝ) := ContinuousMap.const I c with hF
  set Ht := Circle.isCoveringMap_exp.liftHomotopy H F H_0 with hHt
  have hlifts : ∀ p : I × I, Circle.exp (Ht p) = H p := fun p =>
    congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H F H_0) p
  have hz : ∀ a : I, Ht (0, a) = c := fun a =>
    Circle.isCoveringMap_exp.liftHomotopy_zero H F H_0 a
  have hcont1 : Continuous fun t : I => Ht (t, 1) := Ht.continuous.comp (by fun_prop)
  have hcont0 : Continuous fun t : I => Ht (t, 0) := Ht.continuous.comp (by fun_prop)
  have hd := sub_eq_sub_of_circleExp_eq hcont1 hcont0
    (fun t => by rw [hlifts, hlifts, hloop t]) 1 0
  have hd0 : Ht ((0 : I), (1 : I)) - Ht ((0 : I), (0 : I)) = 0 := by rw [hz, hz]; ring
  have hd1 : Ht ((1 : I), (1 : I)) = Ht ((1 : I), (0 : I)) := by
    simp only at hd; linarith [hd, hd0]
  have hcontH1 : Continuous fun s : I => Ht (1, s) := Ht.continuous.comp (by fun_prop)
  have h2 := sub_eq_sub_of_circleExp_eq hθ hcontH1 (fun s => by rw [hlift, hlifts]) 1 0
  simp only at h2
  linarith

/-- A complex number of norm one other than `-1` lies in the slit plane. -/
theorem mem_slitPlane_of_norm_one {u : ℂ} (h : ‖u‖ = 1) (h2 : u ≠ -1) :
    u ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hc
  push_neg at hc
  obtain ⟨hre, him⟩ := hc
  apply h2
  have h3 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h4 : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, h]; norm_num
    simpa [Complex.normSq_apply, sq] using h4
  have : u.re = -1 := by nlinarith [him, sq_nonneg u.re]
  apply Complex.ext <;> simp [this, him]

/-- **Brouwer's fixed point theorem in dimension 2**, complex form: every continuous self-map
of the closed unit disk in `ℂ` has a fixed point. -/
theorem brouwer_2d_complex (f : ℂ → ℂ) (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall (0 : ℂ) 1) (closedBall 0 1)) :
    ∃ z ∈ closedBall (0 : ℂ) 1, f z = z := by
  by_contra hcon
  push_neg at hcon
  have hne : ∀ z ∈ closedBall (0:ℂ) 1, z - f z ≠ 0 := fun z hz h =>
    hcon z hz (sub_eq_zero.mp h).symm
  -- the normalized displacement field, a map from the disk to the circle
  set v : ℂ → ℂ := fun z => (z - f z) / (‖z - f z‖ : ℂ) with hv
  have hvnorm : ∀ z ∈ closedBall (0:ℂ) 1, ‖v z‖ = 1 := by
    intro z hz
    have h := hne z hz
    simp only [hv, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (z - f z))]
    exact div_self (norm_ne_zero_iff.mpr h)
  have hvcont : ContinuousOn v (closedBall (0:ℂ) 1) := by
    apply ContinuousOn.div (continuousOn_id.sub hf)
    · exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_id.sub hf).norm
    · intro z hz
      simpa using norm_ne_zero_iff.mpr (hne z hz)
  -- on the boundary circle, `v z` is never the antipode of `z`
  have hanti : ∀ z : ℂ, ‖z‖ = 1 → (starRingEnd ℂ) z * v z ≠ -1 := by
    intro z hz h
    have hzD : z ∈ closedBall (0:ℂ) 1 := by simp [mem_closedBall, hz]
    have hr : (0:ℝ) < ‖z - f z‖ := norm_pos_iff.mpr (hne z hzD)
    have hrne : ((‖z - f z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hzz : (starRingEnd ℂ) z * z = 1 := by
      rw [mul_comm, Complex.mul_conj]; norm_cast; simp [Complex.normSq_eq_norm_sq, hz]
    have h' : (starRingEnd ℂ) z * (z - f z) = -((‖z - f z‖ : ℝ) : ℂ) := by
      simp only [hv] at h
      field_simp at h
      linear_combination h
    have key : (starRingEnd ℂ) z * f z = ((1 + ‖z - f z‖ : ℝ) : ℂ) := by
      push_cast
      linear_combination hzz - h'
    have h1 : ‖(starRingEnd ℂ) z * f z‖ ≤ 1 := by
      rw [norm_mul, RCLike.norm_conj, hz, one_mul]
      simpa [mem_closedBall] using hmaps hzD
    rw [key, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    linarith
  -- the homotopy `(t, s) ↦ v (t * e ^ (2 π i s))` from a constant loop to `v` on the boundary
  set eps : I → Circle := fun s => Circle.exp (2 * Real.pi * s) with heps
  have hepsc : Continuous eps := Circle.exp.continuous.comp (by fun_prop)
  set γ : I × I → ℂ := fun p => (p.1 : ℝ) • ((eps p.2 : Circle) : ℂ) with hγ
  have hγc : Continuous γ :=
    Continuous.smul (by fun_prop) (continuous_subtype_val.comp (hepsc.comp continuous_snd))
  have hγmem : ∀ p : I × I, γ p ∈ closedBall (0:ℂ) 1 := by
    intro p
    simp only [hγ, mem_closedBall, dist_zero_right, norm_smul, Circle.norm_coe, mul_one,
      Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
    exact p.1.2.2
  have hmem : ∀ p : I × I, v (γ p) ∈ Submonoid.unitSphere ℂ := by
    intro p
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hvnorm _ (hγmem p)
  set H : C(I × I, Circle) :=
    ⟨fun p => (⟨v (γ p), hmem p⟩ : Circle),
      Continuous.subtype_mk (hvcont.comp_continuous hγc hγmem) hmem⟩ with hH
  have hHcoe : ∀ p : I × I, ((H p : Circle) : ℂ) = v (γ p) := fun _ => rfl
  have heps01 : eps 0 = 1 ∧ eps 1 = 1 := by
    refine ⟨by simp [heps], ?_⟩
    simp [heps, mul_one, Circle.exp_two_pi]
  have hconst : ∀ s : I, H (0, s) = H (0, 0) := by
    intro s
    apply Circle.ext
    rw [hHcoe, hHcoe]
    simp [hγ]
  have hloop : ∀ t : I, H (t, 0) = H (t, 1) := by
    intro t
    apply Circle.ext
    rw [hHcoe, hHcoe]
    simp only [hγ, heps01.1, heps01.2]
  -- an explicit lift of the terminal loop, of winding number one
  set w : I → ℂ := fun s => (starRingEnd ℂ) ((eps s : Circle) : ℂ) * v ((eps s : Circle) : ℂ)
    with hw
  have hepsmem : ∀ s : I, ((eps s : Circle) : ℂ) ∈ closedBall (0:ℂ) 1 := by
    intro s; simp [mem_closedBall]
  have hwnorm : ∀ s : I, ‖w s‖ = 1 := by
    intro s
    rw [hw]
    simp only [norm_mul, RCLike.norm_conj, Circle.norm_coe, one_mul]
    exact hvnorm _ (hepsmem s)
  have hwslit : ∀ s : I, w s ∈ Complex.slitPlane := fun s =>
    mem_slitPlane_of_norm_one (hwnorm s) (hanti _ (Circle.norm_coe _))
  have hwcont : Continuous w :=
    (Complex.continuous_conj.comp (continuous_subtype_val.comp hepsc)).mul
      (hvcont.comp_continuous (continuous_subtype_val.comp hepsc) hepsmem)
  set θ : I → ℝ := fun s => 2 * Real.pi * s + Complex.arg (w s) with hθdef
  have hθcont : Continuous θ := by
    apply Continuous.add (by fun_prop)
    rw [continuous_iff_continuousAt]
    exact fun s => (Complex.continuousAt_arg (hwslit s)).comp hwcont.continuousAt
  have hlift : ∀ s : I, Circle.exp (θ s) = H (1, s) := by
    intro s
    apply Circle.ext
    rw [hHcoe, Circle.coe_exp]
    have h1 : Complex.exp ((Complex.arg (w s) : ℂ) * Complex.I) = w s := by
      have := Complex.norm_mul_exp_arg_mul_I (w s)
      rw [hwnorm s] at this
      simpa using this
    have h2 : ((eps s : Circle) : ℂ) = Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) := by
      rw [heps]; exact Circle.coe_exp _
    have h3 : γ (1, s) = ((eps s : Circle) : ℂ) := by simp [hγ]
    rw [h3, hθdef]
    push_cast
    rw [add_mul, Complex.exp_add, h1, hw, ← mul_assoc]
    rw [show Complex.exp (((2:ℂ) * Real.pi * s) * Complex.I) = ((eps s : Circle) : ℂ) by
      rw [h2]; push_cast; ring_nf]
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq]
  have hend := lift_endpoint_eq_of_homotopy_from_const H hconst hloop θ hθcont hlift
  rw [hθdef] at hend
  simp only [Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero] at hend
  have hww : w 1 = w 0 := by rw [hw]; simp only [heps01.1, heps01.2]
  rw [hww] at hend
  have := Real.pi_pos
  linarith

/-- **Brouwer's fixed point theorem in dimension 2**: every continuous self-map of the closed
2-disk has a fixed point. -/
theorem brouwer_2d (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f x = x := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr with he
  have hball : ∀ z : ℂ,
      z ∈ closedBall (0:ℂ) 1 ↔ e z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z
    simp [mem_closedBall, dist_zero_right]
  set g : ℂ → ℂ := fun z => e.symm (f (e z)) with hg
  have hgmaps : MapsTo g (closedBall (0:ℂ) 1) (closedBall (0:ℂ) 1) := by
    intro z hz
    have : f (e z) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := hmaps ((hball z).mp hz)
    simpa [hg, mem_closedBall, dist_zero_right] using this
  have hgcont : ContinuousOn g (closedBall (0:ℂ) 1) :=
    e.symm.continuous.comp_continuousOn
      (hf.comp e.continuous.continuousOn fun z hz => (hball z).mp hz)
  obtain ⟨z, hz, hfz⟩ := brouwer_2d_complex g hgcont hgmaps
  refine ⟨e z, (hball z).mp hz, ?_⟩
  have : e (g z) = e z := by rw [hfz]
  simpa [hg] using this

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

