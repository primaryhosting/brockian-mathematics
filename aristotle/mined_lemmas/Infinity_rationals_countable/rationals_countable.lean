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

theorem rationals_countable : Countable ℚ := inferInstance

/-- The rationals are denumerable (countably infinite): an explicit equivalence `ℚ ≃ ℕ`,
from Mathlib's `Denumerable ℚ` instance. -/
