import Mathlib
namespace C3.BSieve4

theorem lf_pos_nine (p : ℕ) : 0 < lF ({0,2,6,8,12,18,20,26,30} : Finset ℕ) p := by
  unfold lF
  split
  · rename_i hp
    have hp2 : 2 ≤ p := hp.two_le
    have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hp0 : (0:ℝ) < p := by linarith
    have hnum : 0 < 1 - (nu ({0,2,6,8,12,18,20,26,30} : Finset ℕ) p : ℝ)/p := by
      have h1 := nu_lt_nine p hp
      have h2 : ((nu ({0,2,6,8,12,18,20,26,30} : Finset ℕ) p : ℝ)) < p := by exact_mod_cast h1
      rw [sub_pos, div_lt_one hp0]
      exact h2
    have hden : 0 < (1 - 1/(p:ℝ))^({0,2,6,8,12,18,20,26,30} : Finset ℕ).card := by
      apply pow_pos
      have : 1/(p:ℝ) ≤ 1/2 := by
        apply div_le_div_of_nonneg_left <;> linarith
      linarith
    exact div_pos hnum hden
  · norm_num

