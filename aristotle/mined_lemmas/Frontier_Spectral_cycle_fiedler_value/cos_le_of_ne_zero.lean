import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

namespace CycleAux

variable (m : ℕ)

/-- The primitive `(m+3)`-rd root of unity. -/

lemma cos_le_of_ne_zero (k : Fin (m + 3)) (hk : k ≠ 0) :
    Real.cos (2 * Real.pi * (k : ℕ) / ((m + 3 : ℕ) : ℝ))
      ≤ Real.cos (2 * Real.pi / ((m + 3 : ℕ) : ℝ)) := by
  have hpi := Real.pi_pos
  have hklt : (k : ℕ) < m + 3 := k.isLt
  have hk1 : 1 ≤ (k : ℕ) := by
    rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
    · exact absurd (Fin.ext h) hk
    · exact h
  set N : ℝ := ((m + 3 : ℕ) : ℝ) with hNdef
  have hN : (0:ℝ) < N := by rw [hNdef]; positivity
  have hkN : ((k : ℕ) : ℝ) + 1 ≤ N := by rw [hNdef]; exact_mod_cast hklt
  have hk1' : (1:ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk1
  have ha0 : (0:ℝ) ≤ 2 * Real.pi / N := by positivity
  by_cases hc : 2 * ((k : ℕ) : ℝ) ≤ N
  · refine Real.cos_le_cos_of_nonneg_of_le_pi ha0 ?_
      ((div_le_div_iff_of_pos_right hN).mpr (by nlinarith))
    rw [div_le_iff₀ hN]; nlinarith
  · push_neg at hc
    have hcos : Real.cos (2 * Real.pi * ((k : ℕ) : ℝ) / N)
        = Real.cos (2 * Real.pi * (N - ((k : ℕ) : ℝ)) / N) := by
      rw [← Real.cos_two_pi_sub]
      congr 1
      field_simp
    rw [hcos]
    refine Real.cos_le_cos_of_nonneg_of_le_pi ha0 ?_
      ((div_le_div_iff_of_pos_right hN).mpr (by nlinarith))
    rw [div_le_iff₀ hN]; nlinarith

