/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Complex

namespace Math

/-- The two primitive 6-th roots of unity, written explicitly. -/
private noncomputable def zA : ℂ := (1 + Complex.I * (Real.sqrt 3 : ℝ)) / 2
private noncomputable def zB : ℂ := (1 - Complex.I * (Real.sqrt 3 : ℝ)) / 2


private lemma isPrimitiveRoot_six_iff (z : ℂ) :
    IsPrimitiveRoot z 6 ↔ z ^ 2 - z + 1 = 0 := by
  constructor
  · intro h
    have h6 : z ^ 6 = 1 := h.pow_eq_one
    have hfac : (z ^ 2 - z + 1) * ((z ^ 2 + z + 1) * (z ^ 2 - 1)) = 0 := by
      linear_combination h6
    rcases mul_eq_zero.1 hfac with h1 | h2
    · exact h1
    · rcases mul_eq_zero.1 h2 with ha | hb
      · exact absurd (show z ^ 3 = 1 by linear_combination (z - 1) * ha)
          (h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
      · exact absurd (show z ^ 2 = 1 by linear_combination hb)
          (h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  · intro h
    have h3 : z ^ 3 = -1 := by linear_combination (z + 1) * h
    refine IsPrimitiveRoot.mk_of_lt z (by norm_num) (by linear_combination (z ^ 3 - 1) * h3)
      (fun l hl0 hl6 hl => ?_)
    interval_cases l
    · rw [pow_one] at hl
      rw [hl] at h; norm_num at h
    · have hz : z = 2 := by linear_combination hl - h
      rw [hz] at h; norm_num at h
    · rw [h3] at hl; norm_num at hl
    · have hz : z = -1 := by linear_combination z * h3 - hl
      rw [hz] at h; norm_num at h
    · have hz : z = 0 := by linear_combination (-1 : ℂ) * h - hl + z ^ 2 * h3
      rw [hz] at h; norm_num at h

