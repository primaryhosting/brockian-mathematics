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

/-
# Omega Add Omega
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_add_omega
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Omega Add Omega
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_add_omega
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

/-- Ordinal arithmetic: `ω + ω = ω * 2`.

Here `ω` is `Ordinal.omega0`, the first infinite ordinal (in current Mathlib the name
`Ordinal.omega` denotes the omega-indexing order embedding, so `omega0` is the correct
spelling of the ordinal `ω`). -/
theorem omega_add_omega : omega0 + omega0 = omega0 * 2 := by
  rw [show (2 : Ordinal) = 1 + 1 from by norm_num, mul_add, mul_one]

end Ordinal

