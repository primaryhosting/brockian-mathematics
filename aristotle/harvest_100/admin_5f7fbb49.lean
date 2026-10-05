import Mathlib

/-!
# Cardinal Lt Power
Category: Frontier — Set Theory
Target: Infinity.cardinal_lt_power
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace Infinity

/-- **Cantor's cardinal inequality**: for every cardinal `c`, we have `c < 2 ^ c`.

The proof is Mathlib's `Cardinal.cantor`, whose content is Cantor's diagonal
argument: there is no surjection from a type onto its power set. -/
theorem cardinal_lt_power (c : Cardinal.{u}) : c < 2 ^ c :=
  Cardinal.cantor c

end Infinity

#print axioms Infinity.cardinal_lt_power

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

