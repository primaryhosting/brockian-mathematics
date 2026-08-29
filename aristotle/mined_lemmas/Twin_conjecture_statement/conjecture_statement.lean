/-
# Conjecture Statement
Category: Frontier — Prime Numbers
Target: Twin.conjecture_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Conjecture Statement
Category: Frontier — Prime Numbers
Target: Twin.conjecture_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Twin

/-- The twin prime conjecture, *stated only*: for every `N : ℕ` there is a prime `p > N`
such that `p + 2` is also prime. -/

theorem conjecture_statement : TwinPrimeConj ↔ TwinPrimeConj := Iff.rfl

end Twin

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

