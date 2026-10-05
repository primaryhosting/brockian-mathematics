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

namespace Zeta23Scaffold

/-- The cubic weight `psi`. -/
def psiCubic (m : ℕ) : ℚ :=
  (m : ℚ) / 2 + (2 * (m : ℚ) ^ 2 - (m : ℚ) ^ 3) / 18 + (if m = 1 then 4 / 9 else 0)

/-- For `m ≥ 2` the indicator vanishes and
`18 * (1 - psiCubic m) = (m - 2) * (m - 3) * (m + 3)`. -/
theorem eighteen_mul_one_sub_psiCubic (m : ℕ) (hm : 2 ≤ m) :
    18 * (1 - psiCubic m) = ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) + 3) := by
  have h1 : m ≠ 1 := by omega
  simp only [psiCubic, h1, if_false]
  ring

/-- `psiCubic m ≤ 1` for every integer `m ≥ 1`. -/
theorem psiCubic_le_one (m : ℕ) (hm : 1 ≤ m) : psiCubic m ≤ 1 := by
  rcases eq_or_lt_of_le hm with h | h
  · rw [← h]; norm_num [psiCubic]
  · have hm2 : 2 ≤ m := h
    have key := eighteen_mul_one_sub_psiCubic m hm2
    have hfac : (0 : ℚ) ≤ ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) + 3) := by
      have hpos : (0 : ℚ) < (m : ℚ) + 3 := by positivity
      have hprod : (0 : ℚ) ≤ ((m : ℚ) - 2) * ((m : ℚ) - 3) := by
        rcases eq_or_lt_of_le hm2 with h2 | h2
        · rw [← h2]; norm_num
        · have hm3 : 3 ≤ m := h2
          rcases eq_or_lt_of_le hm3 with h3 | h3
          · rw [← h3]; norm_num
          · have hm4 : (4 : ℚ) ≤ (m : ℚ) := by exact_mod_cast h3
            nlinarith
      positivity
    nlinarith [key, hfac]

end Zeta23Scaffold

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

