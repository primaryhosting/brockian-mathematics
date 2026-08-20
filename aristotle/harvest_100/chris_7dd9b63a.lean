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
theorem num_den_injective :
    Function.Injective (fun q : ℚ => (q.num, q.den)) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Rat.ext h.1 h.2

/-- The rationals form a countable type.

Proved directly: `ℤ × ℕ` is countable and `q ↦ (q.num, q.den)` is an injection of `ℚ`
into it. (Mathlib also provides this instance directly.) -/
theorem rationals_countable : Countable ℚ :=
  Function.Injective.countable num_den_injective

/-- The rationals are denumerable (countably infinite): there is an explicit
equivalence `ℚ ≃ ℕ`. -/
noncomputable def ratDenumerable : Denumerable ℚ := inferInstance

/-- An explicit bijection between `ℚ` and `ℕ`. -/
def ratEquivNat : ℚ ≃ ℕ := Denumerable.eqv ℚ

/-- The cardinality of `ℚ` is `ℵ₀`. -/
theorem mk_rat_eq_aleph0 : Cardinal.mk ℚ = Cardinal.aleph0 := Cardinal.mkRat

/-- `ℚ` is infinite, so countability here means countably infinite, not finite. -/
theorem rationals_infinite : Infinite ℚ := inferInstance

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

