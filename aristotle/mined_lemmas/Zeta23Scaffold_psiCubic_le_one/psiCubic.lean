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

/-- Key factorization: for `m ≥ 2` (indicator vanishing),
`18 * (1 - psiCubic m) = (m - 2) * (m - 3) * (m + 3)`. -/
