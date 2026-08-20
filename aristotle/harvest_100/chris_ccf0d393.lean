/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Metric Complex

namespace Math

noncomputable section

/-- If `x` lies on the unit circle, `w` lies in the closed unit disk and `w ≠ x`, then the
vector `x - w` makes an acute angle with `x`. -/
lemma re_sub_mul_conj_pos {x w : ℂ} (hx : ‖x‖ = 1) (hw : ‖w‖ ≤ 1) (hne : w ≠ x) :
    0 < ((x - w) * (starRingEnd ℂ) x).re := by
  have hx' : x.re ^ 2 + x.im ^ 2 = 1 := by
    have h := Complex.sq_norm x
    rw [hx] at h
    simpa [Complex.normSq_apply, sq] using h.symm
  have hw' : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    have h1 := Complex.sq_norm w
    have h2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    rw [h1] at h2
    simpa [Complex.normSq_apply, sq] using h2
  have hne' : 0 < (x.re - w.re) ^ 2 + (x.im - w.im) ^ 2 := by
    have hxw : x - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h1 : 0 < ‖x - w‖ ^ 2 := by positivity
    rw [Complex.sq_norm] at h1
    simpa [Complex.normSq_apply, sq] using h1
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  nlinarith

/-- **Brouwer's fixed point theorem in dimension 2**: every continuous self-map of the closed
unit disk in `ℂ ≃ ℝ²` has a fixed point. -/
theorem brouwer_2d (f : ℂ → ℂ) (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : Set.MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ z ∈ closedBall (0 : ℂ) 1, f z = z := by
  by_contra hcon
  push_neg at hcon
  haveI : SimplyConnectedSpace (closedBall (0 : ℂ) 1) := by
    have := Metric.contractibleSpace_closedBall (E := ℂ) (x := 0) (r := 1) zero_le_one
    infer_instance
  haveI : LocPathConnectedSpace (closedBall (0 : ℂ) 1) :=
    (convex_closedBall (0 : ℂ) 1).locPathConnectedSpace ℂ
  have hfc : Continuous fun x : closedBall (0 : ℂ) 1 => f x := hf.restrict
  have hne : ∀ x : closedBall (0 : ℂ) 1, (x : ℂ) - f x ≠ 0 := fun x =>
    sub_ne_zero.mpr (hcon x x.2).symm
  -- the normalized displacement map, a continuous map from the disk to the unit circle
  set u : C(closedBall (0 : ℂ) 1, Circle) :=
    ⟨fun x => ⟨((x : ℂ) - f x) / (‖(x : ℂ) - f x‖ : ℂ), by
        simpa [Submonoid.unitSphere, mem_sphere_iff_norm] using hne x⟩, by
      apply Continuous.subtype_mk
      apply Continuous.div ((continuous_subtype_val).sub hfc)
        (Complex.continuous_ofReal.comp ((continuous_subtype_val).sub hfc).norm)
      intro x
      simpa using Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hne x))⟩ with hu
  -- lift it through the covering map `Circle.exp`
  obtain ⟨G, ⟨-, hG⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts u ⟨1, by simp⟩
      (Complex.arg (u ⟨1, by simp⟩ : ℂ)) (Circle.exp_arg _)
  have hGu : ∀ x : closedBall (0 : ℂ) 1, Circle.exp (G x) = u x := fun x => congrFun hG x
  -- the boundary circle, parametrized by angle
  set P : ℝ → closedBall (0 : ℂ) 1 := fun s =>
    ⟨Complex.exp (s * Complex.I), by
      simp [norm_exp_ofReal_mul_I]⟩ with hP
  have hPc : Continuous P := by
    apply Continuous.subtype_mk
    exact Complex.continuous_exp.comp (by fun_prop)
  set k : ℝ → ℝ := fun s => G (P s) - s with hk
  have hkc : Continuous k := (G.continuous.comp hPc).sub continuous_id
  -- the key positivity: the lifted angle stays within a quarter turn of the identity
  have hcos : ∀ s, 0 < Real.cos (k s) := by
    intro s
    set x : ℂ := Complex.exp (s * Complex.I) with hx
    have hxnorm : ‖x‖ = 1 := norm_exp_ofReal_mul_I s
    have h1 : Complex.exp ((G (P s) : ℝ) * Complex.I) = (x - f x) / (‖x - f x‖ : ℂ) := by
      have := congrArg (fun c : Circle => (c : ℂ)) (hGu (P s))
      simpa [Circle.coe_exp, hu, hP] using this
    have hconj : Complex.exp ((-s : ℝ) * Complex.I) = (starRingEnd ℂ) x := by
      rw [hx, ← Complex.exp_conj]
      push_cast
      ring_nf
      simp [Complex.conj_I]
    have h2 : Complex.exp ((k s : ℝ) * Complex.I)
        = ((x - f x) * (starRingEnd ℂ) x) / (‖x - f x‖ : ℂ) := by
      have : ((k s : ℝ) : ℂ) * Complex.I
          = ((G (P s) : ℝ) : ℂ) * Complex.I + ((-s : ℝ) : ℂ) * Complex.I := by
        simp [hk]; ring
      rw [this, Complex.exp_add, h1, hconj]
      ring
    have hd : (0:ℝ) < ‖x - f x‖ := norm_pos_iff.mpr (hne (P s))
    have h3 : Real.cos (k s) = ((x - f x) * (starRingEnd ℂ) x).re / ‖x - f x‖ := by
      rw [← Complex.exp_ofReal_mul_I_re (k s), h2]
      rw [Complex.div_re]
      simp [Complex.normSq_ofReal]
      field_simp
    rw [h3]
    apply div_pos _ hd
    refine re_sub_mul_conj_pos hxnorm ?_ ?_
    · have := hmaps (P s).2
      simpa [mem_closedBall_zero_iff] using this
    · exact hcon x (P s).2
  -- but the lifted angle drops by a full turn along the boundary circle
  have hper : P (2 * Real.pi) = P 0 := by
    apply Subtype.ext
    simp [hP, Complex.exp_two_pi_mul_I]
  have hend : k (2 * Real.pi) = k 0 - 2 * Real.pi := by
    simp [hk, hper]
  -- intermediate value theorem produces a point where the cosine is `-1`
  set c := k 0
  set m : ℤ := ⌊(c - Real.pi) / (2 * Real.pi)⌋
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hle : (2 * m + 1) * Real.pi ≤ c := by
    have := Int.floor_le ((c - Real.pi) / (2 * Real.pi))
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [this]
  have hge : c - 2 * Real.pi < (2 * m + 1) * Real.pi := by
    have := Int.lt_floor_add_one ((c - Real.pi) / (2 * Real.pi))
    rw [div_lt_iff₀ (by positivity)] at this
    nlinarith [this]
  have hmem : (2 * m + 1) * Real.pi ∈ Set.Icc (k (2 * Real.pi)) (k 0) := by
    constructor <;> [nlinarith [hend]; nlinarith]
  obtain ⟨s, -, hs⟩ :=
    intermediate_value_Icc' (by positivity : (0:ℝ) ≤ 2 * Real.pi) hkc.continuousOn hmem
  have : Real.cos (k s) = -1 := by
    rw [hs]
    have : (2 * (m:ℝ) + 1) * Real.pi = Real.pi + (m : ℝ) * (2 * Real.pi) := by ring
    rw [this, Real.cos_add_int_mul_two_pi, Real.cos_pi]
  have := hcos s
  linarith [this]

/-- The same statement with the closed 2-disk realized inside `EuclideanSpace ℝ (Fin 2)`. -/
theorem brouwer_2d_euclideanSpace (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : Set.MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f z = z := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
  have hmem : ∀ z : ℂ, e z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      z ∈ closedBall (0 : ℂ) 1 := by
    intro z
    simp
  have hgc : ContinuousOn (fun z : ℂ => e.symm (f (e z))) (closedBall 0 1) := by
    apply e.symm.continuous.comp_continuousOn
    apply hf.comp e.continuous.continuousOn
    intro z hz
    exact (hmem z).2 hz
  have hgm : Set.MapsTo (fun z : ℂ => e.symm (f (e z))) (closedBall 0 1) (closedBall 0 1) := by
    intro z hz
    have h : f (e z) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := hmaps ((hmem z).2 hz)
    simpa using h
  obtain ⟨z, hz, hfz⟩ := brouwer_2d _ hgc hgm
  refine ⟨e z, (hmem z).2 hz, ?_⟩
  have := congrArg e hfz
  simpa using this

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

