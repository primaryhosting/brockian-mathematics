import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem poly_le_two_pow (B E : ℕ) : ∃ t : ℕ, 1 ≤ t ∧ B * (t + 1) ^ E ≤ 2 ^ t := by
  have h := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) E (r := 2) (by norm_num)
  have hc : (0 : ℝ) < 1 / ((B : ℝ) + 1) / 2 ^ E := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h.def hc)
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  set t := max N 1 with ht
  have ht1 : 1 ≤ t := le_max_right _ _
  have hb := hN t (le_max_left _ _)
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) ^ E),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ t)] at hb
  have key : (B : ℝ) * ((t : ℝ) + 1) ^ E ≤ 2 ^ t := by
    have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
    have h3 : ((t : ℝ) + 1) ^ E ≤ (2 * (t : ℝ)) ^ E := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have hfin : (B : ℝ) * 2 ^ E * (1 / ((B : ℝ) + 1) / 2 ^ E * 2 ^ t)
        = ((B : ℝ) / ((B : ℝ) + 1)) * 2 ^ t := by field_simp
    calc (B : ℝ) * ((t : ℝ) + 1) ^ E ≤ (B : ℝ) * (2 * (t : ℝ)) ^ E := by
          nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * (t : ℝ)) E]
      _ = ((B : ℝ) * 2 ^ E) * (t : ℝ) ^ E := by rw [mul_pow]; ring
      _ ≤ ((B : ℝ) * 2 ^ E) * (1 / ((B : ℝ) + 1) / 2 ^ E * 2 ^ t) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ((B : ℝ) / ((B : ℝ) + 1)) * 2 ^ t := hfin
      _ ≤ 2 ^ t := by
          have h1 : (B : ℝ) / ((B : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) t]
  exact_mod_cast key

/-- Choice of the parameters: `n = 2m+1` inputs and `t` rounds in the approximation. -/
