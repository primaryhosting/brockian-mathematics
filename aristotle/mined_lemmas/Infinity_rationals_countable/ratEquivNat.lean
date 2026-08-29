/-
# Rationals Countable
Category: Frontier — Set Theory
Target: Infinity.rationals_countable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`,
-- since Lean 4 requires all commands, including module docstrings, to follow the imports.)

import Mathlib

namespace Infinity

/-- The rationals are countable: `ℚ` is a `Countable` type.
Closed by Mathlib's existing instance (`Rat.instCountable`/`Denumerable.rat`). -/

def ratEquivNat : ℚ ≃ ℕ := Denumerable.eqv ℚ

/-- The cardinality of `ℚ` is `ℵ₀`; this is Mathlib's `Cardinal.mkRat`. -/
