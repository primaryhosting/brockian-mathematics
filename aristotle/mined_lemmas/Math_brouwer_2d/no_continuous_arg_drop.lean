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

set_option grind.warning false

namespace Math

open Complex Metric Set

/-- If `u` lies in the closed unit disk of `ℂ` and `u ≠ 1`, then `u.re < 1`. -/

lemma no_continuous_arg_drop {ph : ℝ → ℝ} (hcont : Continuous ph)
    (hcos : ∀ t, 0 < Real.cos (ph t)) (hper : ph (2 * Real.pi) = ph 0 - 2 * Real.pi) : False := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  set c := ph 0 with hc
  set n : ℤ := ⌊(c - Real.pi) / (2 * Real.pi)⌋ with hn
  set y : ℝ := Real.pi + (n : ℝ) * (2 * Real.pi) with hy
  have h2pi : (0:ℝ) < 2 * Real.pi := by linarith
  have hfl : (n : ℝ) ≤ (c - Real.pi) / (2 * Real.pi) := Int.floor_le _
  have hfl2 : (c - Real.pi) / (2 * Real.pi) < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hy_le : y ≤ c := by
    have := (le_div_iff₀ h2pi).mp hfl
    simp only [hy]
    linarith
  have hy_ge : c - 2 * Real.pi ≤ y := by
    have := (div_lt_iff₀ h2pi).mp hfl2
    simp only [hy]
    linarith
  have hsub := intermediate_value_Icc' (le_of_lt h2pi) hcont.continuousOn (f := ph)
  obtain ⟨t, -, ht⟩ := hsub (show y ∈ Set.Icc (ph (2 * Real.pi)) (ph 0) from
    Set.mem_Icc.mpr ⟨by rw [hper]; linarith, hy_le⟩)
  have hpos := hcos t
  rw [ht, hy, Real.cos_add_int_mul_two_pi, Real.cos_pi] at hpos
  linarith

/-- **Brouwer's fixed point theorem in dimension 2**, complex form: every continuous self-map
of the closed unit disk of `ℂ` has a fixed point. -/
