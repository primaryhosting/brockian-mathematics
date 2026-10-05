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
def ratEquivNat : ℚ ≃ ℕ := Denumerable.eqv ℚ

/-- The cardinality of `ℚ` is `ℵ₀`; this is Mathlib's `Cardinal.mkRat`. -/
theorem mk_rat_eq_aleph0 : Cardinal.mk ℚ = Cardinal.aleph0 := Cardinal.mkRat

end Infinity

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

