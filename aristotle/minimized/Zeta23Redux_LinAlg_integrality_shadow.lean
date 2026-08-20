import Mathlib
/-!
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Redux.LinAlg

/-- Montgomery's integrality step: for every natural number `m`, `2 * m ≤ m ^ 2 + 1`,
which is the shadow of `(m - 1) ^ 2 ≥ 0`. -/

theorem integrality_shadow (m : ℕ) : 2 * m ≤ m ^ 2 + 1 := by
  nlinarith [sq_nonneg ((m : ℤ) - 1)]

/-- Integer form of the same statement: `(m : ℤ) ^ 2 ≥ 2 * m - 1`. -/
