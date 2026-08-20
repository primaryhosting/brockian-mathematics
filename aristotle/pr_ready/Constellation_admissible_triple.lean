/-!
# Admissible Triple
Category: Frontier — Prime Numbers
Target: Constellation.admissible_triple
Statement: The prime triple (5,7,11) is a prime constellation of pattern (0,2,6): Nat.Prime 5, Nat.Prime 7, Nat.Prime 11, with 7 = 5+2 and 11 = 5+6.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Constellation

/-- The prime triple `(5, 7, 11)` is a prime constellation of pattern `(0, 2, 6)`:
`5`, `7`, `11` are all prime, `7 = 5 + 2` and `11 = 5 + 6`. -/
theorem admissible_triple :
    Nat.Prime 5 ∧ Nat.Prime 7 ∧ Nat.Prime 11 ∧ 7 = 5 + 2 ∧ 11 = 5 + 6 :=
  ⟨by norm_num, by norm_num, by norm_num, rfl, rfl⟩

end Constellation

