import Mathlib
/-!
# Rationals Countable
Category: Frontier — Set Theory
Target: Infinity.rationals_countable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- The rationals are a countable type. -/

theorem rationals_countable : Countable ℚ := inferInstance

/-- The rationals are denumerable, i.e. countably infinite. -/
