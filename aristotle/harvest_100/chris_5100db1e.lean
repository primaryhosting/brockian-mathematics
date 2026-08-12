/-
# Psi Cubic Le One
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_le_one
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Psi Cubic Le One
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_le_one
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Scaffold

/-- The cubic weight `psi`. -/
def psiCubic (m : ℕ) : ℚ :=
  (m : ℚ) / 2 + (2 * (m : ℚ) ^ 2 - (m : ℚ) ^ 3) / 18 + (if m = 1 then 4 / 9 else 0)

/-- Key identity: for `m ≥ 2` the indicator vanishes and
`18 * (1 - psiCubic m) = (m - 2) * (m - 3) * (m + 3)`. -/
lemma eighteen_mul_one_sub_psiCubic (m : ℕ) (hm : 2 ≤ m) :
    18 * (1 - psiCubic m) = ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) + 3) := by
  have hne : m ≠ 1 := by omega
  simp only [psiCubic, hne, if_false, add_zero]
  ring

/-- `psi(m) ≤ 1` for all integers `m ≥ 1`. -/
theorem psiCubic_le_one : ∀ m : ℕ, 1 ≤ m → psiCubic m ≤ 1 := by
  intro m hm
  rcases eq_or_lt_of_le hm with h1 | h1
  · subst_vars
    norm_num [psiCubic]
  · have hm2 : 2 ≤ m := h1
    have hkey := eighteen_mul_one_sub_psiCubic m hm2
    have hpos : (0 : ℚ) ≤ ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) + 3) := by
      have h3 : (0 : ℚ) < (m : ℚ) + 3 := by positivity
      have hprod : (0 : ℚ) ≤ ((m : ℚ) - 2) * ((m : ℚ) - 3) := by
        rcases Nat.lt_or_ge m 4 with h | h
        · interval_cases m <;> norm_num
        · have h4 : (4 : ℚ) ≤ (m : ℚ) := by exact_mod_cast h
          nlinarith
      positivity
    linarith [hkey, hpos]

end Zeta23Scaffold

