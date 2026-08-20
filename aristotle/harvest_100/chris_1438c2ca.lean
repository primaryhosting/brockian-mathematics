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
theorem rationals_denumerable : Nonempty (ℚ ≃ ℕ) :=
  ⟨Denumerable.eqv ℚ⟩

/-- The cardinality of `ℚ` is `ℵ₀` (Mathlib's `Cardinal.mkRat`). -/
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

