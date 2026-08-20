import Mathlib
namespace C4.BS5


theorem lf_pos_ten (p : ℕ) : 0 < lF ({0,2,6,8,12,18,20,26,30,32} : Finset ℕ) p := by
  rw [lF]
  split
  · rename_i hp
    have hp2 : 2 ≤ p := hp.two_le
    have hnu : nu ({0,2,6,8,12,18,20,26,30,32} : Finset ℕ) p < p := by
      by_cases h : 11 ≤ p
      · calc nu ({0,2,6,8,12,18,20,26,30,32} : Finset ℕ) p
            ≤ ({0,2,6,8,12,18,20,26,30,32} : Finset ℕ).card := Finset.card_image_le
          _ = 10 := by decide
          _ < p := by omega
      · interval_cases p <;> simp_all (config := {decide := true})
    have hppos : (0:ℝ) < p := by
      have : 0 < p := by omega
      exact_mod_cast this
    have hnum : 0 < 1 - (nu ({0,2,6,8,12,18,20,26,30,32} : Finset ℕ) p : ℝ)/p := by
      have : ((nu ({0,2,6,8,12,18,20,26,30,32} : Finset ℕ) p : ℝ))/p < 1 :=
        (div_lt_one hppos).2 (by exact_mod_cast hnu)
      linarith
    have hden : 0 < (1 - 1/(p:ℝ)) := by
      have : 1/(p:ℝ) ≤ 1/2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast hp2
      linarith
    exact div_pos hnum (by positivity)
  · norm_num

/-- For `g ≠ 0` in `ZMod 23`, exactly `21` residues avoid both `0` and `-g`. -/
