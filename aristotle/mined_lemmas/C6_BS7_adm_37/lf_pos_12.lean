import Mathlib
namespace C6.BS7

theorem lf_pos_12 (p : ℕ) : 0 < lF ({0,2,6,8,12,18,20,26,30,32,36,42} : Finset ℕ) p := by
  rw [lF]
  split
  · rename_i hp
    have hp2 : 2 ≤ p := hp.two_le
    have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hnu : nu ({0,2,6,8,12,18,20,26,30,32,36,42} : Finset ℕ) p < p := by
      by_cases h13 : 13 ≤ p
      · calc nu ({0,2,6,8,12,18,20,26,30,32,36,42} : Finset ℕ) p
            ≤ ({0,2,6,8,12,18,20,26,30,32,36,42} : Finset ℕ).card := Finset.card_image_le
          _ = 12 := by decide
          _ < p := by omega
      · interval_cases p <;> revert hp <;> decide
    have hnuR : (nu ({0,2,6,8,12,18,20,26,30,32,36,42} : Finset ℕ) p : ℝ) < (p:ℝ) := by
      exact_mod_cast hnu
    apply div_pos
    · rw [sub_pos, div_lt_one (by linarith)]; exact hnuR
    · exact pow_pos (by rw [sub_pos, div_lt_one (by linarith)]; linarith) _
  · norm_num

/-- A nonempty set of integers occupies at least one residue class mod `p`. -/
