-- /-!
-- # Omega Add Omega
-- Category: Frontier Wave 2 (deeper machinery)
-- Target: Ordinal.omega_add_omega
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)
-- -/

import Mathlib

/-!
# Omega Add Omega
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_add_omega
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

namespace Ordinal

/-- `ω + ω = ω * 2`, where `ω = Ordinal.omega0` is the first infinite ordinal.
The proof writes `2 = 1 + 1` and uses left distributivity of ordinal
multiplication over addition. -/
theorem omega_add_omega : Ordinal.omega0 + Ordinal.omega0 = Ordinal.omega0 * 2 := by
  have h2 : (2 : Ordinal) = 1 + 1 := by norm_num
  rw [h2, mul_add, mul_one]

end Ordinal

