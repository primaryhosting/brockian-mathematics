import Mathlib
namespace C2.BSieve3

theorem lf_pos_eight (p : ℕ) : 0 < localFactor ({0,2,6,8,12,18,20,26} : Finset ℕ) p := by
  by_cases hp : p.Prime
  · have h2 : 2 ≤ p := hp.two_le
    have hp0 : (0:ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le two_pos h2
    have hnu : nu ({0,2,6,8,12,18,20,26} : Finset ℕ) p < p := by
      rcases le_or_gt p 8 with h | h
      · interval_cases p <;> first | (exfalso; revert hp; decide) | decide
      · exact lt_of_le_of_lt (le_trans Finset.card_image_le (by decide)) h
    rw [localFactor, if_pos hp]
    apply div_pos
    · rw [sub_pos, div_lt_one hp0]
      exact_mod_cast hnu
    · apply pow_pos
      rw [sub_pos, div_lt_one hp0]
      exact_mod_cast h2
  · rw [localFactor, if_neg hp]; norm_num

/-- The number of residues occupied by `G` mod `p` is at most both `|G|` and `p`. -/
