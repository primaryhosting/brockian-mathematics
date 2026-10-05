import Mathlib

/-!
# The circle-valued spin space

The spin space of the classical XY model is the circle `Spin = ℝ / 2πℤ`, a compact
abelian group carrying a translation invariant (Haar) measure.  This file sets up the
cosine and sine functions on `Spin` together with the elementary trigonometric facts
used in the Mermin–Wagner argument.
-/

namespace Phys

noncomputable section

open MeasureTheory

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

lemma spinWave_grad_bound {R : ℕ} (hR : 1 ≤ R) (x : Site d) (i : Fin d) :
    |spinWave R x - spinWave R (x + unitVec i)|
      ≤ 1 / ((max (snorm x : ℝ) 1) * Real.log (1 + (R : ℝ))) := by
  have hL : 0 < Real.log (1 + (R : ℝ)) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  set r : ℕ := snorm x with hr
  set r' : ℕ := snorm (x + unitVec i) with hr'
  have h1 : r ≤ r' + 1 := snorm_le_snorm_add_unit x i
  have h2 : r' ≤ r + 1 := snorm_add_unit_le x i
  have hmax : |spinWave R x - spinWave R (x + unitVec i)|
      ≤ |Real.log (1 + (r':ℝ)) - Real.log (1 + (r:ℝ))| / Real.log (1 + (R:ℝ)) := by
    unfold spinWave
    rw [← hr, ← hr', max_comm 0 _, max_comm 0 _]
    refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
    apply le_of_eq
    rw [show (1 - Real.log (1 + (r:ℝ)) / Real.log (1 + (R:ℝ)))
        - (1 - Real.log (1 + (r':ℝ)) / Real.log (1 + (R:ℝ)))
        = (Real.log (1 + (r':ℝ)) - Real.log (1 + (r:ℝ))) / Real.log (1 + (R:ℝ)) from by ring,
      abs_div, abs_of_pos hL]
  refine le_trans hmax ?_
  have hkey : |Real.log (1 + (r':ℝ)) - Real.log (1 + (r:ℝ))| ≤ 1 / (max (r:ℝ) 1) := by
    rcases le_total r r' with hle | hle
    · have hmono : Real.log (1 + (r:ℝ)) ≤ Real.log (1 + (r':ℝ)) := by
        apply Real.log_le_log (by positivity)
        have : (r:ℝ) ≤ (r':ℝ) := by exact_mod_cast hle
        linarith
      rw [abs_of_nonneg (by linarith)]
      refine le_trans (log_step_bound r r' h2) ?_
      refine one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) ?_
      rcases le_total (r:ℝ) 1 with h | h
      · rw [max_eq_right h]
        have : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg _
        linarith
      · rw [max_eq_left h]; linarith
    · have hmono : Real.log (1 + (r':ℝ)) ≤ Real.log (1 + (r:ℝ)) := by
        apply Real.log_le_log (by positivity)
        have : (r':ℝ) ≤ (r:ℝ) := by exact_mod_cast hle
        linarith
      rw [abs_of_nonpos (by linarith), neg_sub]
      refine le_trans (log_step_bound r' r h1) ?_
      refine one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) ?_
      have hrr : (r:ℝ) ≤ (r':ℝ) + 1 := by exact_mod_cast h1
      have hr'0 : (0:ℝ) ≤ (r':ℝ) := Nat.cast_nonneg _
      rcases le_total (r:ℝ) 1 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
  have hmaxpos : (0:ℝ) < max (r:ℝ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  rw [show 1 / ((max (r:ℝ) 1) * Real.log (1 + (R:ℝ))) = (1 / max (r:ℝ) 1) / Real.log (1 + (R:ℝ)) by
    field_simp]
  gcongr

/-- The number of sites at sup-distance exactly `r` from the origin is at most `8r`
(for `r ≥ 1`), in dimension `d ≤ 2`. -/
