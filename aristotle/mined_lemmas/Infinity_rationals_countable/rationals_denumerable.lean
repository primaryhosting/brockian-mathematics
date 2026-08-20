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

theorem rationals_denumerable : Nonempty (ℚ ≃ ℕ) :=
  ⟨Denumerable.eqv ℚ⟩

/-- The cardinality of `ℚ` is `ℵ₀` (Mathlib's `Cardinal.mkRat`). -/
