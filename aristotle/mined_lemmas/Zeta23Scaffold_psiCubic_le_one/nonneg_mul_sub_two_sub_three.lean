/-
# Psi Cubic Le One
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_le_one
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The cubic weight `psi`. -/

lemma nonneg_mul_sub_two_sub_three {m : ℕ} (hm : 2 ≤ m) :
    0 ≤ ((m : ℚ) - 2) * ((m : ℚ) - 3) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with h | h | h
  · subst h; norm_num
  · subst h; norm_num
  · have h4 : (4 : ℚ) ≤ (m : ℚ) := by exact_mod_cast h
    nlinarith

/-- `psiCubic m ≤ 1` for every integer `m ≥ 1`. -/
