import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-! ## Basic definitions -/

/-- `HasAP A k` says that the set `A ⊆ ℕ` contains a non-degenerate arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` (with common difference `d > 0`). -/

theorem szemerediDensity_of_le_three {k : ℕ} (hk : k ≤ 3) : SzemerediDensity k :=
  szemerediDensity_of_finitary (szemerediFinitary_of_le_three hk)

end Frontier

#print axioms Frontier.furstenberg_szemeredi
#print axioms Frontier.szemerediDensity_of_finitary
#print axioms Frontier.szemerediDensity_of_le_three

