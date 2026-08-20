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

/-- A continuous real function whose cosine is everywhere positive cannot decrease by `2π`
over an interval: the "winding" obstruction. -/
theorem no_winding_of_cos_pos (u : ℝ → ℝ) (hu : Continuous u)
    (hcos : ∀ t, 0 < Real.cos (u t))
    (hper : u (2 * Real.pi) = u 0 - 2 * Real.pi) : False := by
  have hpi := Real.pi_pos
  set a : ℝ := u 0 with ha
  set m : ℤ := ⌊a / Real.pi - 1 / 2⌋ with hm
  set z : ℝ := ((m : ℝ) + 1 / 2) * Real.pi with hz
  have hcosz : Real.cos z = 0 := by
    rw [Real.cos_eq_zero_iff]
    exact ⟨m, by rw [hz]; ring⟩
  have h1 : (m : ℝ) ≤ a / Real.pi - 1 / 2 := Int.floor_le _
  have h2 : a / Real.pi - 1 / 2 < (m : ℝ) + 1 := Int.lt_floor_add_one _
  have hzle : z ≤ a := by
    rw [hz]
    have : ((m : ℝ) + 1 / 2) * Real.pi ≤ (a / Real.pi) * Real.pi := by
      apply mul_le_mul_of_nonneg_right _ hpi.le
      linarith
    rwa [div_mul_cancel₀ _ hpi.ne'] at this
  have hzgt : a < z + Real.pi := by
    rw [hz]
    have : (a / Real.pi) * Real.pi < ((m : ℝ) + 3 / 2) * Real.pi := by
      apply mul_lt_mul_of_pos_right _ hpi
      linarith
    rw [div_mul_cancel₀ _ hpi.ne'] at this
    linarith [this]
  have hzne : z ≠ a := by
    intro h
    have := hcos 0
    rw [← ha, ← h, hcosz] at this
    exact lt_irrefl _ this
  have hzlt : z < a := lt_of_le_of_ne hzle hzne
  have hmem : z ∈ Icc (u (2 * Real.pi)) (u 0) := by
    constructor
    · rw [hper]; linarith
    · rw [← ha]; linarith
  obtain ⟨t, -, hut⟩ :=
    intermediate_value_Icc' (by positivity : (0:ℝ) ≤ 2 * Real.pi) hu.continuousOn hmem
  have := hcos t
  rw [hut, hcosz] at this
  exact lt_irrefl _ this

/-- On the unit circle, the vector `z - w` (with `‖w‖ ≤ 1`, `w ≠ z`) makes an acute angle
with `z`. -/
theorem re_conj_mul_sub_pos {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1) (hne : w ≠ z) :
    0 < ((starRingEnd ℂ) z * (z - w)).re := by
  have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := congrArg (fun x : ℝ => x ^ 2) hz
    simpa [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt,
      add_nonneg (sq_nonneg z.re) (sq_nonneg z.im)] using this
  have hw2 : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    have h0 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt
      (add_nonneg (sq_nonneg w.re) (sq_nonneg w.im))] at h0
    exact h0
  have key : ((starRingEnd ℂ) z * (z - w)).re
      = z.re * (z.re - w.re) + z.im * (z.im - w.im) := by
    simp [Complex.mul_re]
  rw [key]
  by_contra h
  push_neg at h
  have hre : w.re = z.re ∧ w.im = z.im := by
    constructor <;> nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]
  exact hne (Complex.ext hre.1 hre.2)

/-- **Brouwer's fixed point theorem in dimension 2**: every continuous self-map of the closed
unit disk in `ℂ` (the closed 2-dimensional disk) has a fixed point. -/
theorem brouwer_2d {f : ℂ → ℂ} (hcont : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall (0 : ℂ) 1) (closedBall 0 1)) :
    ∃ z ∈ closedBall (0 : ℂ) 1, f z = z := by
  by_contra hcon
  push_neg at hcon
  haveI : LocPathConnectedSpace (closedBall (0:ℂ) 1) :=
    (convex_closedBall (0:ℂ) 1).locPathConnectedSpace
  haveI : ContractibleSpace (closedBall (0:ℂ) 1) :=
    (convex_closedBall (0:ℂ) 1).contractibleSpace ⟨0, by simp⟩
  have hnz : ∀ x : closedBall (0:ℂ) 1, (x : ℂ) - f x ≠ 0 := fun x =>
    sub_ne_zero_of_ne (Ne.symm (hcon x x.2))
  have hfc : Continuous fun x : closedBall (0:ℂ) 1 => f x := hcont.restrict
  have hgc : Continuous fun x : closedBall (0:ℂ) 1 =>
      ((x : ℂ) - f x) / ((‖(x : ℂ) - f x‖ : ℝ) : ℂ) := by
    apply Continuous.div (continuous_subtype_val.sub hfc)
    · exact Complex.continuous_ofReal.comp ((continuous_subtype_val.sub hfc).norm)
    · intro x
      simpa using hnz x
  have hmemG : ∀ x : closedBall (0:ℂ) 1,
      ((x : ℂ) - f x) / ((‖(x : ℂ) - f x‖ : ℝ) : ℂ) ∈ Submonoid.unitSphere ℂ := by
    intro x
    show _ ∈ Metric.sphere (0:ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm]
    exact div_self (by simpa using hnz x)
  set G : C(closedBall (0:ℂ) 1, Circle) :=
    ⟨fun x => ⟨((x : ℂ) - f x) / ((‖(x : ℂ) - f x‖ : ℝ) : ℂ), hmemG x⟩,
      hgc.subtype_mk hmemG⟩ with hG
  set a₀ : closedBall (0:ℂ) 1 := ⟨0, by simp⟩ with ha₀
  obtain ⟨Θ, ⟨-, hΘ⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts G a₀
    (Complex.arg ((G a₀ : Circle) : ℂ)) (Circle.exp_arg _)
  set P : ℝ → closedBall (0:ℂ) 1 := fun t => ⟨Complex.exp ((t : ℂ) * I), by simp⟩ with hP
  have hPc : Continuous P := by
    apply Continuous.subtype_mk
    fun_prop
  set u : ℝ → ℝ := fun t => Θ (P t) - t with hu
  have hucont : Continuous u := (Θ.continuous.comp hPc).sub continuous_id
  have hkey : ∀ t : ℝ, ((P t : ℂ) - f (P t))
      = ((‖(P t : ℂ) - f (P t)‖ : ℝ) : ℂ) * Complex.exp ((Θ (P t) : ℂ) * I) := by
    intro t
    have h := congrFun hΘ (P t)
    simp only [Function.comp_apply] at h
    have h' : Complex.exp ((Θ (P t) : ℂ) * I)
        = ((P t : ℂ) - f (P t)) / ((‖(P t : ℂ) - f (P t)‖ : ℝ) : ℂ) := by
      have h2 := congrArg Subtype.val h
      rw [show (Subtype.val (Circle.exp (Θ (P t))) : ℂ) = Complex.exp ((Θ (P t) : ℂ) * I) from
        Circle.coe_exp _] at h2
      exact h2
    have hn0 : ((‖(P t : ℂ) - f (P t)‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using hnz (P t)
    rw [h', mul_div_cancel₀ _ hn0]
  have hcos : ∀ t : ℝ, 0 < Real.cos (u t) := by
    intro t
    have hc1 : ‖((P t : ℂ))‖ = 1 := by
      simp [hP]
    have hw1 : ‖f (P t)‖ ≤ 1 := by
      have := hmaps (P t).2
      simpa [mem_closedBall_zero_iff] using this
    have hne : f (P t) ≠ (P t : ℂ) := hcon _ (P t).2
    have hpos := re_conj_mul_sub_pos hc1 hw1 hne
    have hconj : (starRingEnd ℂ) ((P t : ℂ)) = Complex.exp (-(t : ℂ) * I) := by
      show (starRingEnd ℂ) (Complex.exp ((t : ℂ) * I)) = _
      rw [← Complex.exp_conj]; simp
    have hsum : Complex.exp (-(t : ℂ) * I) * Complex.exp ((Θ (P t) : ℂ) * I)
        = Complex.exp (((u t : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add, hu]
      push_cast
      ring_nf
    have hexp : (starRingEnd ℂ) ((P t : ℂ)) * ((P t : ℂ) - f (P t))
        = ((‖(P t : ℂ) - f (P t)‖ : ℝ) : ℂ) * Complex.exp (((u t : ℝ) : ℂ) * I) := by
      rw [hconj]
      conv_lhs => rw [hkey t]
      linear_combination ((‖(P t : ℂ) - f (P t)‖ : ℝ) : ℂ) * hsum
    rw [hexp] at hpos
    rw [Complex.mul_re] at hpos
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re] at hpos
    have hnorm : 0 < ‖(P t : ℂ) - f (P t)‖ := by
      simpa using hnz (P t)
    nlinarith [hpos, hnorm]
  have hper : u (2 * Real.pi) = u 0 - 2 * Real.pi := by
    have hPeq : P (2 * Real.pi) = P 0 := by
      apply Subtype.ext
      simp [hP, Complex.exp_two_pi_mul_I]
    rw [hu]
    simp [hPeq]
  exact no_winding_of_cos_pos u hucont hcos hper

/-- **Brouwer's fixed point theorem in dimension 2**, stated for the closed unit disk of the
Euclidean plane `EuclideanSpace ℝ (Fin 2)`. -/
theorem brouwer_2d_euclidean {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hcont : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f x = x := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
  have hmem : ∀ z : ℂ,
      z ∈ closedBall (0:ℂ) 1 ↔ e z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z
    simp [e.norm_map]
  have hcont' : ContinuousOn (fun w : ℂ => e.symm (f (e w))) (closedBall 0 1) :=
    e.symm.continuous.comp_continuousOn
      (hcont.comp e.continuous.continuousOn fun w hw => (hmem w).1 hw)
  have hmaps' : MapsTo (fun w : ℂ => e.symm (f (e w))) (closedBall (0:ℂ) 1) (closedBall 0 1) := by
    intro w hw
    have h2 := hmaps ((hmem w).1 hw)
    simpa [mem_closedBall_zero_iff, e.symm.norm_map] using h2
  obtain ⟨z, hz, hfz⟩ := brouwer_2d hcont' hmaps'
  refine ⟨e z, (hmem z).1 hz, ?_⟩
  have := congrArg e hfz
  simpa using this

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

