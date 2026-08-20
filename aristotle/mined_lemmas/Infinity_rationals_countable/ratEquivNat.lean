import Mathlib
/-!
# Rationals Countable
Category: Frontier — Set Theory
Target: Infinity.rationals_countable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- A rational number is determined by its numerator and denominator, so the map
`q ↦ (q.num, q.den)` from `ℚ` to `ℤ × ℕ` is injective. -/

def ratEquivNat : ℚ ≃ ℕ := Denumerable.eqv ℚ

/-- The cardinality of `ℚ` is `ℵ₀`. -/
