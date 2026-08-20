import Mathlib
namespace C5.BS6

theorem lf_pos_11 (p : ℕ) : 0 < lF ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p := by
  rw [lF]
  split
  · rename_i hp
    have hp2 : 2 ≤ p := hp.two_le
    have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hppos : (0:ℝ) < (p:ℝ) := by linarith
    have hnu : nu ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p < p := nu_lt_of_prime p hp
    have hnuR : (nu ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p : ℝ) < (p:ℝ) := by
      exact_mod_cast hnu
    apply div_pos
    · have : (nu ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p : ℝ) / (p:ℝ) < 1 :=
        (div_lt_one hppos).mpr hnuR
      linarith
    · apply pow_pos
      have : 1 / (p:ℝ) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le <;> linarith
      linarith
  · norm_num

