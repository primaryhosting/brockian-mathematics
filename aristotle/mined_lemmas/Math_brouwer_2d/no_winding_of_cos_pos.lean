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
