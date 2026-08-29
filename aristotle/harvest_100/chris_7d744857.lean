import Mathlib

/-!
# Psi Cubic Le One
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_le_one
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Scaffold

/-- The cubic weight `psi`. -/
def psiCubic (m : ℕ) : ℚ :=
  (m : ℚ) / 2 + (2 * (m : ℚ) ^ 2 - (m : ℚ) ^ 3) / 18 + (if m = 1 then 4 / 9 else 0)

/-- Key factorization: for `m ≥ 2` we have
`18 * (1 - psiCubic m) = (m - 2) * (m - 3) * (m + 3)`. -/
theorem eighteen_mul_one_sub_psiCubic (m : ℕ) (hm : 2 ≤ m) :
    18 * (1 - psiCubic m) = ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) + 3) := by
  have hm1 : m ≠ 1 := by omega
  simp only [psiCubic, hm1, if_false]
  ring

/-- For an integer `m ≥ 2`, `(m - 2) * (m - 3) ≥ 0` over `ℚ`. -/
theorem mul_sub_two_sub_three_nonneg (m : ℕ) (hm : 2 ≤ m) :
    0 ≤ ((m : ℚ) - 2) * ((m : ℚ) - 3) := by
  rcases eq_or_lt_of_le hm with h | h
  · rw [← h]; norm_num
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h3 | h3
    · rw [← h3]; norm_num
    · have h4 : (4 : ℚ) ≤ (m : ℚ) := by exact_mod_cast h3
      nlinarith

/-- `psiCubic m ≤ 1` for every integer `m ≥ 1`. -/
theorem psiCubic_le_one (m : ℕ) (hm : 1 ≤ m) : psiCubic m ≤ 1 := by
  rcases eq_or_lt_of_le hm with h | h
  · simp [psiCubic, ← h]
    norm_num
  · have hm2 : 2 ≤ m := h
    have hkey := eighteen_mul_one_sub_psiCubic m hm2
    have hpos : (0 : ℚ) ≤ (m : ℚ) + 3 := by positivity
    have hnn := mul_sub_two_sub_three_nonneg m hm2
    nlinarith [mul_nonneg hnn hpos]

end Zeta23Scaffold

