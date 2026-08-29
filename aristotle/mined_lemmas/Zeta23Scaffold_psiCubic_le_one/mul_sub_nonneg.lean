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

lemma mul_sub_nonneg (m : Nat) : 0 ≤ ((m : Rat) - 2) * ((m : Rat) - 3) := by
  rcases lt_or_ge m 3 with h | h
  · have h2 : (m : Rat) ≤ 2 := by
      have : m ≤ 2 := by omega
      exact_mod_cast this
    have h3 : (m : Rat) ≤ 3 := by linarith
    nlinarith
  · have h3 : (3 : Rat) ≤ (m : Rat) := by exact_mod_cast h
    nlinarith

/-- `psiCubic m ≤ 1` for all integers `m ≥ 1`. -/
