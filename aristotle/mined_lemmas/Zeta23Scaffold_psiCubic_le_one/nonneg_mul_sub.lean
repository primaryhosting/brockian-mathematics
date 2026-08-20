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

theorem nonneg_mul_sub (m : ℕ) (hm : 2 ≤ m) :
    0 ≤ ((m : ℚ) - 2) * ((m : ℚ) - 3) := by
  rcases eq_or_lt_of_le hm with h | h
  · rw [← h]; norm_num
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h3 | h3
    · rw [← h3]; norm_num
    · have h4 : (4 : ℚ) ≤ (m : ℚ) := by exact_mod_cast h3
      nlinarith

/-- `psiCubic m ≤ 1` for all integers `m ≥ 1`. -/
