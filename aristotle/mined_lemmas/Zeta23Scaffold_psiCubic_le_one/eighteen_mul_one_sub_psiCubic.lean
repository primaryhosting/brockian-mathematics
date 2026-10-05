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

theorem eighteen_mul_one_sub_psiCubic (m : ℕ) (hm : 2 ≤ m) :
    18 * (1 - psiCubic m) = ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) + 3) := by
  have hm1 : m ≠ 1 := by omega
  simp only [psiCubic, hm1, if_false]
  ring

/-- For an integer `m ≥ 2`, `(m - 2) * (m - 3) ≥ 0` over `ℚ`. -/
