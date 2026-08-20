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

theorem psiCubic_le_one (m : ℕ) (hm : 1 ≤ m) : psiCubic m ≤ 1 := by
  rcases eq_or_lt_of_le hm with h1 | h1
  · subst_vars
    norm_num [psiCubic]
  · have hm2 : 2 ≤ m := h1
    have hkey := eighteen_mul_one_sub_psiCubic m hm2
    have hprod := nonneg_mul_sub m hm2
    have hpos : (0 : ℚ) < (m : ℚ) + 3 := by positivity
    nlinarith [mul_nonneg hprod (le_of_lt hpos)]

end Zeta23Scaffold

