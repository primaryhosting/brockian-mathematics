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
