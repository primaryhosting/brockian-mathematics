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

open scoped Real
open Complex Metric Set

namespace Brouwer2D

/-! ### The radial retraction of the plane onto the closed unit disk -/

/-- The radial retraction of `ℂ` onto the closed unit disk. -/

theorem brouwer_complex (f : ℂ → ℂ) (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1)) :
    ∃ z ∈ closedBall (0 : ℂ) 1, f z = z := by
  by_contra hcon
  push_neg at hcon
  have hball : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∈ closedBall (0 : ℂ) 1 := fun z h => by simpa using h
  -- Extend `f` to the whole plane using the radial retraction; the extension has no fixed point.
  set F : ℂ → ℂ := fun z => f (diskProj z) with hF
  have hFc : Continuous F :=
    hf.comp_continuous continuous_diskProj fun z => hball _ (norm_diskProj_le z)
  have hFnorm : ∀ z, ‖F z‖ ≤ 1 := fun z => by
    simpa using hmaps (hball _ (norm_diskProj_le z))
  have hFne : ∀ z, F z ≠ z := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := hz ▸ hFnorm z
    have hp : diskProj z = z := diskProj_eq_self hzn
    exact hcon z (hball _ hzn) (by rw [hF] at hz; simpa [hp] using hz)
  -- A continuous logarithm of the nonvanishing map `z ↦ z - F z`.
  obtain ⟨G, hG⟩ := exists_continuous_log ⟨fun z => z - F z, continuous_id.sub hFc⟩
    fun z => sub_ne_zero.2 fun h => hFne z h.symm
  simp only [ContinuousMap.coe_mk] at hG
  set c : ℝ → ℂ := fun t => Complex.exp (2 * Real.pi * Complex.I * t) with hc
  have hcnorm : ∀ t, ‖c t‖ = 1 := fun t => by simp [hc, Complex.norm_exp]
  set u : ℝ → ℝ := fun t => (G (c t) - 2 * Real.pi * Complex.I * t).im with hu
  have hucont : Continuous u :=
    Complex.continuous_im.comp ((G.continuous.comp (by fun_prop)).sub (by fun_prop))
  -- The imaginary part of the lift stays in the region where the cosine is positive.
  have hcos : ∀ t, 0 < Real.cos (u t) := by
    intro t
    have h1 : Complex.exp (G (c t) - 2 * Real.pi * Complex.I * t)
        = (c t - F (c t)) * (starRingEnd ℂ) (c t) := by
      rw [Complex.exp_sub, hG]
      rw [show Complex.exp (2 * Real.pi * Complex.I * t) = c t from rfl,
        div_eq_mul_inv, Complex.inv_eq_conj (hcnorm t)]
    have h2 : 0 < ((c t - F (c t)) * (starRingEnd ℂ) (c t)).re :=
      re_sub_mul_conj_pos (hcnorm t) (hFnorm _) (hFne _)
    rw [← h1, Complex.exp_re] at h2
    nlinarith [Real.exp_pos (G (c t) - 2 * Real.pi * Complex.I * t).re]
  -- But going once around the circle decreases that imaginary part by `2π`.
  have hc0 : c 0 = 1 := by simp [hc]
  have hc1 : c 1 = 1 := by simp [hc]
  have hu0 : u 0 = (G 1).im := by simp [hu, hc0]
  have hu1 : u 1 = (G 1).im - 2 * Real.pi := by simp [hu, hc1]
  have hmem : u 0 - Real.pi ∈ Icc (u 1) (u 0) := by
    constructor <;> [linarith [Real.pi_pos, hu0, hu1]; linarith [Real.pi_pos]]
  obtain ⟨t, -, hut⟩ := intermediate_value_Icc' zero_le_one hucont.continuousOn hmem
  have hneg := hcos t
  rw [hut, Real.cos_sub_pi] at hneg
  linarith [hcos 0]

end Brouwer2D

namespace Math

/-- **Brouwer's fixed point theorem in dimension two**: every continuous self-map of the
closed unit disk in the Euclidean plane has a fixed point. -/
