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

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 8000

open Finset

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d` of `n` with `d` coprime to `n / d`. -/

theorem sixth_of_infinite (h : {n : ℕ | IsUnitaryPerfect n}.Infinite) :
    ∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect := by
  obtain ⟨n, hn, hn2⟩ := (h.diff knownUnitaryPerfect.finite_toSet).nonempty
  exact ⟨n, hn, hn2⟩

end Brockian.UnitaryPerfect

