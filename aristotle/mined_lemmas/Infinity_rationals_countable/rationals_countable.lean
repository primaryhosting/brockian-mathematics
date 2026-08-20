/-
# Rationals Countable
Category: Frontier — Set Theory
Target: Infinity.rationals_countable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rationals Countable
Category: Frontier — Set Theory
Target: Infinity.rationals_countable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- The rationals form a countable type (Mathlib instance `Rat.instCountable`,
derived from `Encodable ℚ`). -/

theorem rationals_countable : Countable ℚ := inferInstance

/-- The rationals are denumerable (countably infinite): there is an explicit
equivalence `ℚ ≃ ℕ`, via Mathlib's `Denumerable ℚ` instance. -/
