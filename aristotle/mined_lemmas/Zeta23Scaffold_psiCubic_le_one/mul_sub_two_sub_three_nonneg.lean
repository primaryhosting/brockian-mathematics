import Mathlib

/-!
# Psi Cubic Le One
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_le_one
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Zeta23Scaffold

/-- The cubic weight `psi`. -/

lemma mul_sub_two_sub_three_nonneg (m : ℕ) (hm : 2 ≤ m) :
    0 ≤ ((m : ℚ) - 2) * ((m : ℚ) - 3) := by
  rcases eq_or_lt_of_le hm with h | h
  · rw [← h]; norm_num
  · rcases eq_or_lt_of_le (show 3 ≤ m by omega) with h3 | h3
    · rw [← h3]; norm_num
    · have h4 : (4 : ℚ) ≤ (m : ℚ) := by exact_mod_cast h3
      nlinarith

/-- `psi(m) ≤ 1` for all integers `m ≥ 1`. -/
